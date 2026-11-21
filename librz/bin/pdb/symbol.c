// SPDX-FileCopyrightText: 2023 billow <billow.fun@gmail.com>
// SPDX-License-Identifier: LGPL-3.0-only

#include "symbol.h"

#include "pdb.h"

RZ_IPI bool PDBSectionOffset_parse(RzBuffer *b, PDBSectionOffset *section_offset) {
	if (!section_offset) {
		return false;
	}
	ut32 offset = 0;
	ut16 section_index = 0;
	if (!(rz_buf_read_le32(b, &offset) &&
		    rz_buf_read_le16(b, &section_index))) {
		return false;
	}
	section_offset->section_index = section_index;
	section_offset->offset = offset;
	return true;
}

static bool symbol_name_parse(RzBuffer *b, PDBSymbolKind kind, char **result) {
	if (kind < S_ST_MAX) {
		return buf_read_u8_pascal_string(b, result);
	} else {
		return rz_buf_read_string(b, result) > 0;
	}
	return false;
}

RZ_IPI bool PDBSData_parse(RzBuffer *b, PDBSymbolKind kind, PDBSData *sdata) {
	if (!sdata) {
		return false;
	}

	if (!(rz_buf_read_le32(b, &sdata->type_index) &&
		    PDBSectionOffset_parse(b, &sdata->offset) &&
		    symbol_name_parse(b, kind, &sdata->name))) {
		return false;
	}

	switch (kind) {
	case S_GMANDATA:
	case S_GMANDATA_ST:
		sdata->managed = true;
		sdata->global = true;
		break;
	case S_GDATA32:
	case S_GDATA32_ST:
		sdata->global = true;
		break;
	case S_LMANDATA:
	case S_LMANDATA_ST:
		sdata->managed = true;
		break;
	default: break;
	}
	return true;
}

RZ_IPI bool PDBSPublic_parse(RzBuffer *b, PDBSymbolKind kind, PDBSPublic *s) {
	map_err(b && s);
	ut32 flags = 0;
	map_err(rz_buf_read_le32(b, &flags) &&
		PDBSectionOffset_parse(b, &s->offset) &&
		symbol_name_parse(b, kind, &s->name));
	s->code = flags & cvpsfCode;
	s->function = flags & cvpsfFunction;
	s->managed = flags & cvpsfManaged;
	s->msil = flags & cvpsfMSIL;
	return true;
err:
	return false;
}

static bool PDBSProcedure_parse(RzBuffer *b, PDBSymbolKind kind, PDBSProcedure *s) {
	map_err(rz_buf_read_le32(b, &s->parent) &&
		rz_buf_read_le32(b, &s->end) &&
		rz_buf_read_le32(b, &s->next) &&
		rz_buf_read_le32(b, &s->length) &&
		rz_buf_read_le32(b, &s->debug_start) &&
		rz_buf_read_le32(b, &s->debug_end) &&
		rz_buf_read_le32(b, &s->type_index) &&
		PDBSectionOffset_parse(b, &s->offset) &&
		rz_buf_read8(b, &s->flags) &&
		symbol_name_parse(b, kind, &s->name));
	s->global = kind == S_GPROC32 || kind == S_GPROC32_ID;
	s->id = kind == S_GPROC32_ID || kind == S_LPROC32_ID;
	return true;
err:
	return false;
}

static bool PDBSFrameProcedure_parse(RzBuffer *b, PDBSFrameProcedure *s) {
	map_err(rz_buf_read_le32(b, &s->frame_size) &&
		rz_buf_read_le32(b, &s->padding_size) &&
		rz_buf_read_le32(b, &s->padding_offset) &&
		rz_buf_read_le32(b, &s->saved_registers_size) &&
		PDBSectionOffset_parse(b, &s->exception_handler) &&
		rz_buf_read_le32(b, &s->flags));
	s->local_base_pointer = (s->flags >> 14) & 3;
	s->param_base_pointer = (s->flags >> 16) & 3;
	return true;
err:
	return false;
}

static bool PDBSLocal_parse(RzBuffer *b, PDBSymbolKind kind, PDBSLocal *s) {
	map_err(rz_buf_read_le32(b, &s->type_index) &&
		rz_buf_read_le16(b, &s->flags) &&
		symbol_name_parse(b, kind, &s->name));
	s->param = s->flags & 0x0001;
	s->optimized_out = s->flags & 0x0100;
	return true;
err:
	return false;
}

static bool PDBSDefRange_parse(RzBuffer *b, PDBSymbolKind kind, PDBSDefRange *s) {
	ut32 offset = 0;
	ut16 flags = 0;
	switch (kind) {
	case S_DEFRANGE_REGISTER:
		return rz_buf_read_le16(b, &s->register_index);
	case S_DEFRANGE_REGISTER_REL:
		map_err(rz_buf_read_le16(b, &s->register_index) && rz_buf_read_le16(b, &flags));
		// fallthrough
	default:
		map_err(rz_buf_read_le32(b, &offset));
		s->offset = (st32)offset;
		return true;
	}
err:
	return false;
}

static int PDBSDefRange_kind(PDBSymbolKind kind) {
	switch (kind) {
	case S_DEFRANGE_REGISTER: return PDB_DefRangeRegister;
	case S_DEFRANGE_FRAMEPOINTER_REL: return PDB_DefRangeFramePointerRelative;
	case S_DEFRANGE_FRAMEPOINTER_REL_FULL_SCOPE: return PDB_DefRangeFramePointerRelativeFullScope;
	default: return PDB_DefRangeRegisterRelative;
	}
}

static bool PDBSRegisterRelative_parse(RzBuffer *b, PDBSymbolKind kind, PDBSRegisterRelative *s) {
	ut32 offset = 0;
	map_err(rz_buf_read_le32(b, &offset) &&
		rz_buf_read_le32(b, &s->type_index) &&
		(kind == S_BPREL32 || rz_buf_read_le16(b, &s->register_index)) &&
		symbol_name_parse(b, kind, &s->name));
	s->offset = (st32)offset;
	return true;
err:
	return false;
}

static bool PDBSRegisterVariable_parse(RzBuffer *b, PDBSymbolKind kind, PDBSRegisterVariable *s) {
	return rz_buf_read_le32(b, &s->type_index) &&
		rz_buf_read_le16(b, &s->register_index) &&
		symbol_name_parse(b, kind, &s->name);
}

static bool PDBSInlineSite_parse(RzBuffer *b, PDBSInlineSite *s) {
	return rz_buf_read_le32(b, &s->parent) &&
		rz_buf_read_le32(b, &s->end) &&
		rz_buf_read_le32(b, &s->inlinee);
}

RZ_IPI bool PDBSymbol_parse(RzBuffer *b, PDBSymbol *symbol) {
	if (!symbol) {
		return false;
	}
	map_err(rz_buf_read_le16(b, &symbol->raw_kind));

	switch (symbol->raw_kind) {
	case S_LDATA32:
	case S_LDATA32_ST:
	case S_GDATA32:
	case S_GDATA32_ST:
	case S_LMANDATA:
	case S_LMANDATA_ST:
	case S_GMANDATA:
	case S_GMANDATA_ST:
		symbol->kind = PDB_Data;
		symbol->data = RZ_NEW0(PDBSData);
		map_err(symbol->data);
		map_err(PDBSData_parse(b, symbol->raw_kind, symbol->data));
		break;
	case S_PUB32:
	case S_PUB32_ST:
		symbol->kind = PDB_Public;
		symbol->data = RZ_NEW0(PDBSPublic);
		map_err(symbol->data);
		map_err(PDBSPublic_parse(b, symbol->raw_kind, symbol->data));
		break;
	case S_GPROC32:
	case S_LPROC32:
	case S_GPROC32_ID:
	case S_LPROC32_ID:
		symbol->kind = PDB_Procedure;
		symbol->data = RZ_NEW0(PDBSProcedure);
		map_err(symbol->data);
		map_err(PDBSProcedure_parse(b, symbol->raw_kind, symbol->data));
		break;
	case S_FRAMEPROC:
		symbol->kind = PDB_FrameProcedure;
		symbol->data = RZ_NEW0(PDBSFrameProcedure);
		map_err(symbol->data);
		map_err(PDBSFrameProcedure_parse(b, symbol->data));
		break;
	case S_LOCAL:
		symbol->kind = PDB_Local;
		symbol->data = RZ_NEW0(PDBSLocal);
		map_err(symbol->data);
		map_err(PDBSLocal_parse(b, symbol->raw_kind, symbol->data));
		break;
	case S_DEFRANGE_REGISTER:
	case S_DEFRANGE_FRAMEPOINTER_REL:
	case S_DEFRANGE_FRAMEPOINTER_REL_FULL_SCOPE:
	case S_DEFRANGE_REGISTER_REL:
		symbol->kind = PDBSDefRange_kind(symbol->raw_kind);
		symbol->data = RZ_NEW0(PDBSDefRange);
		map_err(symbol->data);
		map_err(PDBSDefRange_parse(b, symbol->raw_kind, symbol->data));
		break;
	case S_REGREL32:
	case S_BPREL32:
		symbol->kind = symbol->raw_kind == S_REGREL32 ? PDB_RegisterRelative : PDB_BasePointerRelative;
		symbol->data = RZ_NEW0(PDBSRegisterRelative);
		map_err(symbol->data);
		map_err(PDBSRegisterRelative_parse(b, symbol->raw_kind, symbol->data));
		break;
	case S_REGISTER:
		symbol->kind = PDB_RegisterVariable;
		symbol->data = RZ_NEW0(PDBSRegisterVariable);
		map_err(symbol->data);
		map_err(PDBSRegisterVariable_parse(b, symbol->raw_kind, symbol->data));
		break;
	case S_INLINESITE:
		symbol->kind = PDB_InlineSite;
		symbol->data = RZ_NEW0(PDBSInlineSite);
		map_err(symbol->data);
		map_err(PDBSInlineSite_parse(b, symbol->data));
		break;
	default:
		RZ_LOG_DEBUG("unimplemented symbol kind: 0x%" PFMT32x "\n", symbol->raw_kind);
		break;
	}

	return true;
err:
	return false;
}

RZ_IPI bool PDBSymbolTable_iter(PDBSymbolTable *symbol_table, PDBSymbolIter *iter) {
	map_err(symbol_table && iter);
	iter->b = rz_buf_new_with_buf(symbol_table->b);
	return true;
err:
	return false;
}

RZ_IPI PDBSymbol *PDBSymbolTable_symbol_by_index(PDBSymbolTable *symbol_table, PDBSymbolIndex index) {
	PDBSymbolIter iter = { 0 };
	PDBSymbol *symbol = NULL;
	map_err(PDBSymbolTable_iter(symbol_table, &iter));
	map_err(PDBSymbolIter_seek(&iter, index));
	symbol = RZ_NEW0(PDBSymbol);
	map_err(symbol);
	map_err(PDBSymbolIter_next(&iter, symbol));

	return symbol;
err:
	free(symbol);
	return NULL;
}

static void PDBSymbol_data_free(PDBSymbol *symbol) {
	if (!symbol->data) {
		return;
	}
	switch (symbol->kind) {
	case PDB_Public: free(((PDBSPublic *)symbol->data)->name); break;
	case PDB_Data: free(((PDBSData *)symbol->data)->name); break;
	case PDB_Procedure: free(((PDBSProcedure *)symbol->data)->name); break;
	case PDB_Local: free(((PDBSLocal *)symbol->data)->name); break;
	case PDB_RegisterRelative:
	case PDB_BasePointerRelative: free(((PDBSRegisterRelative *)symbol->data)->name); break;
	case PDB_RegisterVariable: free(((PDBSRegisterVariable *)symbol->data)->name); break;
	default: break;
	}
	RZ_FREE(symbol->data);
}

RZ_IPI bool PDBSymbolIter_next(PDBSymbolIter *iter, PDBSymbol *symbol) {
	if (!iter) {
		return false;
	}
	RzBuffer *b = NULL;

	while (rz_buf_tell(iter->b) < rz_buf_size(iter->b)) {
		PDBSymbolIndex index = rz_buf_tell(iter->b);
		ut16 length = 0;
		map_err(rz_buf_read_le16(iter->b, &length));
		if (length < 2) {
			return false;
		}
		const ut64 begin = rz_buf_tell(iter->b);
		rz_buf_seek(iter->b, length, RZ_BUF_CUR);
		if (!symbol) {
			goto loop_continue;
		}

		b = rz_buf_new_slice(iter->b, begin, length);
		map_err(b);
		symbol->index = index;
		symbol->length = length;
		if (!PDBSymbol_parse(b, symbol)) {
			// Skips a record that is shorter than its kind needs.
			PDBSymbol_data_free(symbol);
			goto loop_continue;
		}

		switch (symbol->raw_kind) {
		case S_ALIGN:
		case S_SKIP:
			goto loop_continue;
		default:
			if (!symbol->data) {
				goto loop_continue;
			}
			rz_buf_free(b);
			return true;
		}
	loop_continue:
		rz_buf_free(b);
		b = NULL;
	}
err:
	rz_buf_free(b);
	return false;
}

RZ_IPI bool PDBSymbolIter_seek(PDBSymbolIter *iter, PDBSymbolIndex index) {
	map_err(iter);
	rz_buf_seek(iter->b, index, RZ_BUF_SET);
	return true;
err:
	return false;
}

static void PDBSymbol_free(void *x) {
	if (!x) {
		return;
	}
	PDBSymbol *symbol = x;
	PDBSymbol_data_free(symbol);
	free(symbol);
}

RZ_IPI bool PDBSymbolIter_collect(PDBSymbolIter *iter, RzPVector /*<PDBSymbol *>*/ **psymbols) {
	RzPVector *symbols = *psymbols = rz_pvector_new(PDBSymbol_free);
	if (!symbols) {
		return false;
	}
	while (true) {
		PDBSymbol *symbol = RZ_NEW0(PDBSymbol);
		if (!symbol) {
			rz_pvector_free(symbols);
			psymbols = NULL;
			return false;
		}
		if (!PDBSymbolIter_next(iter, symbol)) {
			break;
		}
		rz_pvector_push(symbols, symbol);
	}
	return true;
}

RZ_API bool rz_pdb_all_symbols_foreach(
	RZ_BORROW RZ_NONNULL RzPdb *pdb,
	RZ_BORROW RZ_NONNULL bool (*f)(RzPdb *, const PDBSymbol *, void *),
	RZ_BORROW RZ_NULLABLE void *u) {
	rz_return_val_if_fail(pdb && f, false);
	if (!(pdb->s_gdata && pdb->s_gdata->global_symbols)) {
		return true;
	}
	void **it;
	rz_pvector_foreach (pdb->s_gdata->global_symbols, it) {
		if (!f(pdb, *it, u)) {
			return false;
		}
	}
	if (!pdb->module_infos) {
		return true;
	}
	void **modit;
	rz_pvector_foreach (pdb->module_infos, modit) {
		PDBModuleInfo *modi = *modit;
		if (!modi->symbols) {
			continue;
		}
		rz_pvector_foreach (modi->symbols, it) {
			if (!f(pdb, *it, u)) {
				return false;
			}
		}
	}
	return true;
}
