// SPDX-FileCopyrightText: 2020 HoundThe <cgkajm@gmail.com>
// SPDX-FileCopyrightText: 2021 Basstorm <basstorm@nyist.edu.cn>
// SPDX-License-Identifier: LGPL-3.0-only

#include <rz_bin.h>
#include <rz_core.h>
#include <rz_type.h>
#include <rz_pdb.h>
#include "analysis_private.h"
#include "../bin/pdb/pdb.h"

static RzType *pdb_type_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type, char *name);
static RzType *modifier_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type);
static RzType *pointer_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type, char *name);
static RzType *procedure_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type, char *name);
static RzType *array_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type);
static void arglist_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *arglist, RzPVector /*<RzCallableArg *>*/ *vec);
static RzType *mfunction_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info, char *name);
static RzType *onemethod_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info);
static RzType *member_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info, char *name, ut64 *bitfield_width);
static RzType *nest_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *t, char *name);
static RzType *union_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type);
static RzTypeUnionMember *union_member_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info);
static RzType *class_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type);
static RzTypeStructMember *class_member_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *t);
static RzType *enum_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type);
static RzTypeEnumCase *enumerate_parse(RzPdbTpiType *type);
static RzType *pdb_simple_type_parse(const RzTypeDB *typedb, const RzPdbTpiType *type);

static bool is_parsable_type(const RzPdbTpiType *t) {
	const RzPDBTpiKind k = t->kind;
	return k == TpiKind_CLASS ||
		k == TpiKind_UNION ||
		k == TpiKind_ENUM;
}

/**
 * \brief Create a type name from offset
 *
 * \param offset
 * \return char* Name or NULL if error
 */
static char *create_type_name_from_offset(ut64 offset) {
	int offset_length = snprintf(NULL, 0, "type_0x%" PFMT64x, offset);
	char *str = malloc(offset_length + 1);
	snprintf(str, offset_length + 1, "type_0x%" PFMT64x, offset);
	return str;
}

static RzType *pdb_simple_type_parse(const RzTypeDB *typedb, const RzPdbTpiType *type) {
	rz_warn_if_fail(type->kind == TpiKind_SIMPLE_TYPE);
	const Tpi_LF_SimpleType *simple_type = type->data;
	char *error_msg = NULL;
	RzType *typ = rz_type_parse_string_single(typedb->parser, simple_type->type, &error_msg);
	if (error_msg) {
		RZ_LOG_ERROR("%s : Error parsing complex type member \"%s\" type:\n%s\n",
			__FUNCTION__, simple_type->type, error_msg);
		RZ_FREE(error_msg);
	}
	return typ;
}

static RzType *array_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type) {
	rz_return_val_if_fail(type && stream && typedb, NULL);
	Tpi_LF_Array *lf_array = type->data;
	RzPdbTpiType *element = rz_bin_pdb_get_type_by_index(stream, lf_array->element_type);
	if (!element) {
		return NULL;
	}
	RzType *element_type = pdb_type_parse(typedb, stream, element, NULL);
	if (!element_type) {
		return NULL;
	}
	RzType *typ = RZ_NEW0(RzType);
	if (!typ) {
		return NULL;
	}
	typ->kind = RZ_TYPE_KIND_ARRAY;
	typ->array.type = element_type;
	typ->array.count = rz_bin_pdb_get_type_val(type);
	return typ;
}

static RzType *modifier_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type) {
	rz_return_val_if_fail(type && stream && typedb, NULL);
	Tpi_LF_Modifier *lf_modifier = type->data;
	RzPdbTpiType *m_utype = rz_bin_pdb_get_type_by_index(stream, lf_modifier->modified_type);
	if (m_utype) {
		RzType *typ = pdb_type_parse(typedb, stream, m_utype, NULL);
		if (typ && lf_modifier->umodifier.const_) {
			switch (typ->kind) {
			case RZ_TYPE_KIND_IDENTIFIER:
				typ->identifier.is_const = true;
				break;
			case RZ_TYPE_KIND_POINTER:
				typ->pointer.is_const = true;
				break;
			default:
				break;
			}
		}
		return typ;
	}
	return NULL;
}

static RzType *pointer_parse(
	const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type, char *name) {
	rz_return_val_if_fail(type && typedb, NULL);
	Tpi_LF_Pointer *lf_pointer = type->data;
	RzType *typ = RZ_NEW0(RzType);
	if (!typ) {
		goto error;
	}
	typ->kind = RZ_TYPE_KIND_POINTER;
	RzPdbTpiType *p_utype = rz_bin_pdb_get_type_by_index(stream, lf_pointer->utype);
	if (p_utype) {
		RzType *tmp = pdb_type_parse(typedb, stream, p_utype, name);
		if (!tmp) {
			goto error;
		}
		typ->pointer.type = tmp;
		return typ;
	}
error:
	rz_type_free(typ);
	return NULL;
}

static void arglist_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *arglist, RzPVector /*<RzCallableArg *>*/ *vec) {
	rz_return_if_fail(arglist && typedb && vec);
	Tpi_LF_Arglist *lf_arglist = arglist->data;
	ut32 *ptr_types = lf_arglist->arg_type;
	for (int i = 0; i < lf_arglist->count; i++) {
		RzPdbTpiType *stype = rz_bin_pdb_get_type_by_index(stream, *ptr_types++);
		if (!stype) {
			continue;
		}
		RzType *type = pdb_type_parse(typedb, stream, stype, NULL);
		if (!type) {
			continue;
		}
		RzCallableArg *arg = RZ_NEW0(RzCallableArg);
		arg->name = rz_str_newf("arg%d", i);
		arg->type = type;
		rz_pvector_push(vec, arg);
	}
}

static RzType *procedure_parse(
	const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type, char *name) {
	rz_return_val_if_fail(type && stream && typedb, NULL);
	Tpi_LF_Procedure *lf_procedure = type->data;
	RzType *typ = RZ_NEW0(RzType);
	RzCallable *callable = RZ_NEW0(RzCallable);
	if (!typ || !callable) {
		free(typ);
		free(callable);
		return NULL;
	}
	typ->kind = RZ_TYPE_KIND_CALLABLE;
	typ->callable = callable;
	if (!name) {
		typ->callable->name = create_type_name_from_offset(type->index);
	} else {
		typ->callable->name = rz_str_dup(name);
	}

	typ->callable->cc = rz_bin_pdb_calling_convention_as_string(lf_procedure->func_attr.calling_convention);
	// parse return type
	RzPdbTpiType *ret_type = rz_bin_pdb_get_type_by_index(stream, lf_procedure->return_type);
	if (ret_type) {
		typ->callable->ret = pdb_type_parse(typedb, stream, ret_type, name);
		if (!typ->callable->ret) {
			typ->callable->noret = true;
		}
	}
	// parse parameter list
	typ->callable->args = rz_pvector_new((RzPVectorFree)rz_type_callable_arg_free);
	if (!typ->callable->args) {
		rz_type_free(typ);
		return NULL;
	}
	RzPdbTpiType *arglist = rz_bin_pdb_get_type_by_index(stream, lf_procedure->arg_list);
	if (arglist) {
		arglist_parse(typedb, stream, arglist, typ->callable->args);
	}
	if (!rz_type_func_save((RzTypeDB *)typedb, callable)) {
		// A callable with this name is already registered. PDB type graphs
		// frequently reference the same procedure type more than once, and
		// unnamed procedures get a deterministic name derived from their TPI
		// offset, so duplicates are expected. rz_type_func_save() does not take
		// ownership on failure, so reuse the already-stored callable and free
		// this one; otherwise it (and its whole subtree) would be leaked.
		RzCallable *existing = rz_type_func_get((RzTypeDB *)typedb, callable->name);
		rz_type_callable_free(callable);
		typ->callable = existing;
		if (!existing) {
			rz_type_free(typ);
			return NULL;
		}
	}
	return typ;
}

static RzType *mfunction_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info, char *name) {
	rz_return_val_if_fail(type_info && stream && typedb, NULL);
	Tpi_LF_MFcuntion *lf_mfunction = type_info->data;
	RzType *type = RZ_NEW0(RzType);
	RzCallable *callable = RZ_NEW0(RzCallable);
	if (!type || !callable) {
		free(type);
		free(callable);
		return NULL;
	}
	type->kind = RZ_TYPE_KIND_CALLABLE;
	type->callable = callable;
	type->callable->name = rz_str_dup(name);
	type->callable->cc = rz_bin_pdb_calling_convention_as_string(lf_mfunction->func_attr.calling_convention);
	// parse return type
	RzPdbTpiType *ret_type = rz_bin_pdb_get_type_by_index(stream, lf_mfunction->return_type);
	if (ret_type) {
		type->callable->ret = pdb_type_parse(typedb, stream, ret_type, name);
		if (!type->callable->ret) {
			type->callable->noret = true;
		}
	}
	// parse parameter list
	type->callable->args = rz_pvector_new((RzPVectorFree)rz_type_callable_arg_free);
	if (!type->callable->args) {
		rz_type_free(type);
		return NULL;
	}
	RzPdbTpiType *arglist = rz_bin_pdb_get_type_by_index(stream, lf_mfunction->arglist);
	if (arglist) {
		arglist_parse(typedb, stream, arglist, type->callable->args);
	}
	if (!rz_type_func_save((RzTypeDB *)typedb, callable)) {
		// See procedure_parse(): rz_type_func_save() does not take ownership when
		// a callable of the same name already exists, so free this duplicate and
		// reuse the stored one to avoid leaking it together with its subtree.
		RzCallable *existing = rz_type_func_get((RzTypeDB *)typedb, callable->name);
		rz_type_callable_free(callable);
		type->callable = existing;
		if (!existing) {
			rz_type_free(type);
			return NULL;
		}
	}
	return type;
}

static RzType *onemethod_parse(
	const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info) {
	rz_return_val_if_fail(type_info && typedb, NULL);
	Tpi_LF_OneMethod *lf_onemethod = type_info->data;
	char *name = rz_bin_pdb_get_type_name(type_info);
	RzPdbTpiType *utype = rz_bin_pdb_get_type_by_index(stream, lf_onemethod->index);
	if (!utype) {
		return NULL;
	}
	if (utype->kind == TpiKind_MFUNCTION) {
		return mfunction_parse(typedb, stream, utype, name);
	}
	return NULL;
}

static RzType *member_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info, char *name, ut64 *bitfield_width) {
	rz_return_val_if_fail(type_info && typedb, NULL);
	Tpi_LF_Member *lf_member = type_info->data;

	RzPdbTpiType *utype = rz_bin_pdb_get_type_by_index(stream, lf_member->field_type);
	if (!utype) {
		return NULL;
	}
	if (utype->kind == TpiKind_BITFIELD) {
		// A bitfield member ("int a : 4;"): resolve the member to its underlying
		// integer type and report the bit width via \p bitfield_width, so it is
		// stored as a bitfield (see RzTypeStructMember.size / RzTypeUnionMember.size).
		Tpi_LF_Bitfield *lf_bitfield = utype->data;
		if (!lf_bitfield) {
			return NULL;
		}
		if (bitfield_width) {
			*bitfield_width = lf_bitfield->length;
		}
		RzPdbTpiType *base = rz_bin_pdb_get_type_by_index(stream, lf_bitfield->base_type);
		if (!base) {
			return NULL;
		}
		return pdb_type_parse(typedb, stream, base, name);
	}
	return pdb_type_parse(typedb, stream, utype, name);
}

static RzType *static_member_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info, char *name) {
	rz_return_val_if_fail(type_info && typedb, NULL);
	Tpi_LF_StaticMember *lf_stmember = type_info->data;
	RzPdbTpiType *utype = rz_bin_pdb_get_type_by_index(stream, lf_stmember->field_type);
	if (!utype) {
		return NULL;
	}
	return pdb_type_parse(typedb, stream, utype, name);
}

static RzType *type_new_identify(const char *name, RzTypeIdentifierKind k) {
	if (RZ_STR_ISEMPTY(name)) {
		return NULL;
	}
	RzType *t = RZ_NEW0(RzType);
	if (!t) {
		return NULL;
	}
	t->kind = RZ_TYPE_KIND_IDENTIFIER;
	t->identifier.name = rz_str_dup(name);
	t->identifier.kind = k;
	return t;
}

static RzTypeIdentifierKind iKind_from_bKind(RzBaseTypeKind k) {
	switch (k) {
	case RZ_BASE_TYPE_KIND_STRUCT: return RZ_TYPE_IDENTIFIER_KIND_STRUCT;
	case RZ_BASE_TYPE_KIND_UNION: return RZ_TYPE_IDENTIFIER_KIND_UNION;
	case RZ_BASE_TYPE_KIND_ENUM: return RZ_TYPE_IDENTIFIER_KIND_ENUM;
	case RZ_BASE_TYPE_KIND_TYPEDEF:
	case RZ_BASE_TYPE_KIND_ATOMIC: return RZ_TYPE_IDENTIFIER_KIND_UNSPECIFIED;
	}
	return RZ_TYPE_IDENTIFIER_KIND_UNSPECIFIED;
}

static RzType *nest_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info, char *name) {
	rz_return_val_if_fail(type_info && stream && typedb, NULL);
	Tpi_LF_NestType *lf_nest = type_info->data;
	RzPdbTpiType *utpi = rz_bin_pdb_get_type_by_index(stream, lf_nest->index);
	if (!utpi) {
		return NULL;
	}
	const char *uname = rz_bin_pdb_get_type_name(utpi);
	if (uname) {
		const RzBaseType *bt = rz_type_db_get_base_type(typedb, uname);
		if (bt) {
			return type_new_identify(bt->name, iKind_from_bKind(bt->kind));
		}
	}

	RzType *utype = pdb_type_parse(typedb, stream, utpi, NULL);
	if (!utype) {
		return NULL;
	}
	return rz_type_clone(utype);
}

/**
 * \brief Parses struct member
 *
 * \param typedb Types DB instance
 * \param stream TPI Stream
 * \param t Current RzPdbTpiType (member)
 * \return RzTypeStructMember* parsed member, NULL if fail
 */
static RzTypeStructMember *class_member_parse(
	const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *t) {
	rz_return_val_if_fail(t, NULL);
	char *name = NULL;
	ut64 offset = 0;
	ut64 bitfield_width = 0;
	RzType *type = NULL;
	switch (t->kind) {
	case TpiKind_ONEMETHOD: {
		name = rz_bin_pdb_get_type_name(t);
		type = onemethod_parse(typedb, stream, t);
		break;
	}
	case TpiKind_MEMBER: {
		offset = rz_bin_pdb_get_type_val(t);
		name = rz_bin_pdb_get_type_name(t);
		type = member_parse(typedb, stream, t, name, &bitfield_width);
		break;
	}
	case TpiKind_STMEMBER: {
		name = rz_bin_pdb_get_type_name(t);
		type = static_member_parse(typedb, stream, t, name);
		break;
	}
	case TpiKind_NESTTYPE: {
		name = rz_bin_pdb_get_type_name(t);
		type = nest_parse(typedb, stream, t, rz_str_dup(name));
		break;
	}
	case TpiKind_VBCLASS:
	case TpiKind_BCLASS:
		// For structure, we don't need base class for now
		goto cleanup;
	case TpiKind_METHOD:
		// TODO: need to handle overloaded methods here
		goto cleanup;
	case TpiKind_VFUNCTAB:
		// For structure, we don't need vtable for now
		goto cleanup;
	default:
		rz_warn_if_reached();
		RZ_LOG_ERROR("%s : unsupported leaf type 0x%x\n", __FUNCTION__, t->leaf);
		goto cleanup;
	}
	if (!type) {
		RZ_LOG_INFO("%s : couldn't parse structure member type!\n", __FUNCTION__);
		return NULL;
	}

	RzTypeStructMember *member = RZ_NEW0(RzTypeStructMember);
	if (!member) {
		goto cleanup;
	}
	member->name = rz_str_dup(name);
	member->type = type;
	member->offset = offset;
	member->size = bitfield_width; // bitfield width in bits, 0 if not a bitfield
	return member;
cleanup:
	rz_type_free(type);
	return NULL;
}

static inline bool is_tpitype_unnamed(const char *name) {
	return !name || !strcmp(name, "<unnamed-tag>") || !strcmp(name, "<anonymous-tag>");
}

static inline RzBaseType *get_tpitype_basetype(const RzTypeDB *typedb, RzPdbTpiType *type, const char *name) {
	RzBaseType *base_type;
	if (is_tpitype_unnamed(name)) {
		char *tmp_name = create_type_name_from_offset(type->index);
		base_type = rz_type_db_get_base_type(typedb, tmp_name);
		free(tmp_name);
	} else {
		base_type = rz_type_db_get_base_type(typedb, name);
	}
	return base_type;
}

static RzType *create_rztype(RzPdbTpiType *type, RzTypeIdentifierKind kind, const char *name) {
	RzType *t = RZ_NEW0(RzType);
	if (!t) {
		return NULL;
	}
	t->kind = RZ_TYPE_KIND_IDENTIFIER;
	t->identifier.kind = kind;
	t->identifier.name = is_tpitype_unnamed(name) ? create_type_name_from_offset(type->index) : rz_str_dup(name);
	return t;
}

#define PDB_PROCESS_LF_INDEX \
	if (member_info->kind == TpiKind_INDEX) { \
		ut32 index = rz_bin_pdb_get_type_val(member_info); \
		if (index == type->index) { \
			break; \
		} \
		RzPdbTpiType *t = rz_bin_pdb_get_type_by_index(stream, index); \
		if (!t) { \
			continue; \
		} \
		RzPVector *t_members = rz_bin_pdb_get_type_members(stream, t); \
		if (!t_members) { \
			continue; \
		} \
		members = t_members; \
		goto foreach_members; \
	}

/**
 * \brief Parses structures into BaseType and saves them into hashtable
 *
 * \param t RzTypeDB instance
 * \param stream TPI Stream
 * \param type Current type
 */
static RzType *class_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type) {
	rz_return_val_if_fail(typedb && stream && type, NULL);

	RzBaseType *base_type = NULL;
	char *name = rz_bin_pdb_get_type_name(type);
	if (name) {
		base_type = get_tpitype_basetype(typedb, type, name);
		if (base_type) {
			if (base_type->kind != RZ_BASE_TYPE_KIND_STRUCT) {
				RZ_LOG_WARN("PDB: Type of %s (struct) conflicts with already defined type (%s), redefining it.\n",
					name, rz_type_base_type_kind_as_string(base_type->kind));
				rz_type_db_delete_base_type((RzTypeDB *)typedb, base_type);
				base_type = NULL;
			} else if (type->parsed || rz_bin_pdb_type_is_fwdref(type)) {
				return base_type->type ? rz_type_clone(base_type->type) : create_rztype(type, RZ_TYPE_IDENTIFIER_KIND_STRUCT, name);
			} else if (base_type->attrs != RZ_TYPE_TYPECLASS_INVALID) {
				RZ_LOG_INFO("%s : Redefining type %s.\n", __FUNCTION__, name);
			}
		}
	}

	if (!base_type) {
		base_type = rz_type_base_type_new(RZ_BASE_TYPE_KIND_STRUCT);
		if (!base_type) {
			return NULL;
		}

		RzType *typ = create_rztype(type, RZ_TYPE_IDENTIFIER_KIND_STRUCT, name);
		if (!typ) {
			rz_type_base_type_free(base_type);
			return NULL;
		}
		base_type->type = typ;
		base_type->name = rz_str_dup(typ->identifier.name);
		base_type->attrs = RZ_TYPE_TYPECLASS_INVALID;
		if (!rz_type_db_save_base_type(typedb, base_type)) {
			return NULL;
		}

		if (rz_bin_pdb_type_is_fwdref(type)) {
			return rz_type_clone(base_type->type);
		}
	}
	rz_vector_clear(&base_type->struct_data.members);
	RzPVector *members = rz_bin_pdb_get_type_members(stream, type);
	void **it;
foreach_members:
	rz_pvector_foreach (members, it) {
		RzPdbTpiType *member_info = *it;
		PDB_PROCESS_LF_INDEX;
		RzTypeStructMember *struct_member = class_member_parse(typedb, stream, member_info);
		if (!struct_member) {
			continue; // skip the failure
		}
		void *element = rz_vector_push(&base_type->struct_data.members, struct_member);
		if (!element) {
			rz_warn_if_reached();
			rz_type_base_struct_member_free(struct_member, NULL);
			return NULL;
		}
		free(struct_member);
	}
	base_type->size = rz_bin_pdb_get_type_val(type);
	if (base_type->attrs == RZ_TYPE_TYPECLASS_INVALID) {
		base_type->attrs = RZ_TYPE_TYPECLASS_NONE;
		rz_list_append(stream->print_type, base_type);
	}
	type->parsed = true;
	return base_type->type ? rz_type_clone(base_type->type) : NULL;
}

/**
 * \brief Parses union member
 *
 * \param typedb Types DB instance
 * \param stream TPI Stream
 * \param type_info Current RzPdbTpiType (member)
 * \return RzTypeUnionMember* parsed member, NULL if fail
 */
static RzTypeUnionMember *union_member_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type_info) {
	rz_return_val_if_fail(type_info && stream && typedb, NULL);
	char *name = NULL;
	ut64 offset = 0;
	ut64 bitfield_width = 0;
	RzType *type = NULL;
	switch (type_info->kind) {
	case TpiKind_ONEMETHOD: {
		name = rz_bin_pdb_get_type_name(type_info);
		type = onemethod_parse(typedb, stream, type_info);
		break;
	}
	case TpiKind_MEMBER: {
		offset = rz_bin_pdb_get_type_val(type_info);
		name = rz_bin_pdb_get_type_name(type_info);
		type = member_parse(typedb, stream, type_info, name, &bitfield_width);
		break;
	}
	case TpiKind_NESTTYPE: {
		name = rz_bin_pdb_get_type_name(type_info);
		type = nest_parse(typedb, stream, type_info, rz_str_dup(name));
		break;
	}
	default:
		rz_warn_if_reached();
		RZ_LOG_ERROR("%s : unsupported leaf type 0x%x\n", __FUNCTION__, type_info->leaf);
		goto cleanup;
	}
	if (!type) {
		RZ_LOG_INFO("%s : couldn't parse union member type!\n", __FUNCTION__);
		return NULL;
	}

	RzTypeUnionMember *member = RZ_NEW0(RzTypeUnionMember);
	if (!member) {
		goto cleanup;
	}
	member->name = rz_str_dup(name);
	member->type = type;
	member->offset = offset;
	member->size = bitfield_width; // bitfield width in bits, 0 if not a bitfield
	return member;
cleanup:
	rz_type_free(type);
	return NULL;
}

/**
 * \brief Parses union into BaseType and saves it into hashtable
 * \param typedb Types DB instance
 * \param stream TPI Stream
 * \param type_info Current RzPdbTpiType (enum case)
 */
static RzType *union_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type) {
	rz_return_val_if_fail(typedb && stream && type, NULL);

	RzBaseType *base_type = NULL;
	char *name = rz_bin_pdb_get_type_name(type);
	if (name) {
		base_type = get_tpitype_basetype(typedb, type, name);
		if (base_type) {
			if (base_type->kind != RZ_BASE_TYPE_KIND_UNION) {
				RZ_LOG_WARN("PDB: Type of %s (union) conflicts with already defined type (%s), redefining it.\n",
					name, rz_type_base_type_kind_as_string(base_type->kind));
				rz_type_db_delete_base_type((RzTypeDB *)typedb, base_type);
				base_type = NULL;
			} else if (type->parsed || rz_bin_pdb_type_is_fwdref(type)) {
				return base_type->type ? rz_type_clone(base_type->type) : create_rztype(type, RZ_TYPE_IDENTIFIER_KIND_UNION, name);
			} else if (base_type->attrs != RZ_TYPE_TYPECLASS_INVALID) {
				RZ_LOG_INFO("%s : Redefining type %s.\n", __FUNCTION__, name);
			}
		}
	}

	if (!base_type) {
		base_type = rz_type_base_type_new(RZ_BASE_TYPE_KIND_UNION);
		if (!base_type) {
			return NULL;
		}

		RzType *typ = create_rztype(type, RZ_TYPE_IDENTIFIER_KIND_UNION, name);
		if (!typ) {
			rz_type_base_type_free(base_type);
			return NULL;
		}
		base_type->type = typ;
		base_type->name = rz_str_dup(typ->identifier.name);
		base_type->attrs = RZ_TYPE_TYPECLASS_INVALID;
		if (!rz_type_db_save_base_type(typedb, base_type)) {
			return NULL;
		}

		if (rz_bin_pdb_type_is_fwdref(type)) {
			return rz_type_clone(base_type->type);
		}
	}
	rz_vector_clear(&base_type->union_data.members);
	RzPVector *members = rz_bin_pdb_get_type_members(stream, type);
	void **it;
foreach_members:
	rz_pvector_foreach (members, it) {
		RzPdbTpiType *member_info = *it;
		PDB_PROCESS_LF_INDEX;
		RzTypeUnionMember *union_member = union_member_parse(typedb, stream, member_info);
		if (!union_member) {
			continue; // skip the failure
		}
		void *element = rz_vector_push(&base_type->union_data.members, union_member);
		if (!element) {
			rz_type_base_union_member_free(union_member, NULL);
			return NULL;
		}
		free(union_member);
	}
	base_type->size = rz_bin_pdb_get_type_val(type);
	if (base_type->attrs == RZ_TYPE_TYPECLASS_INVALID) {
		base_type->attrs = RZ_TYPE_TYPECLASS_NONE;
		rz_list_append(stream->print_type, base_type);
	}
	type->parsed = true;
	return base_type->type ? rz_type_clone(base_type->type) : NULL;
}

/**
 * \brief Parse enum case
 * \param type Current type info (enum case)
 * \return RzTypeEnumCase* parsed enum case, NULL if fail
 */
static RzTypeEnumCase *enumerate_parse(RzPdbTpiType *type) {
	rz_return_val_if_fail(type && type->kind == TpiKind_ENUMERATE, NULL);

	// sometimes, the type doesn't have get_val for some reason
	ut64 value = rz_bin_pdb_get_type_val(type);
	char *name = rz_bin_pdb_get_type_name(type);
	RzTypeEnumCase *cas = RZ_NEW0(RzTypeEnumCase);
	if (!cas) {
		goto cleanup;
	}
	cas->name = rz_str_dup(name);
	cas->val = value;
	return cas;
cleanup:
	return NULL;
}

/**
 * \brief Parses enum into BaseType and saves it into SDB
 *
 * \param t RzTypeDB instance
 * \param stream TPI Stream
 * \param type Current type
 */
static RzType *enum_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type) {
	rz_return_val_if_fail(typedb && type, NULL);
	Tpi_LF_Enum *lf_enum = type->data;
	// assert all member functions we need info from
	RzBaseType *base_type = NULL;
	char *name = rz_bin_pdb_get_type_name(type);
	if (name) {
		base_type = get_tpitype_basetype(typedb, type, name);
		if (base_type) {
			if (base_type->kind != RZ_BASE_TYPE_KIND_ENUM) {
				RZ_LOG_WARN("PDB: Type of %s (enum) conflicts with already defined type (%s), redefining it.\n",
					name, rz_type_base_type_kind_as_string(base_type->kind));
				rz_type_db_delete_base_type((RzTypeDB *)typedb, base_type);
				base_type = NULL;
			} else if (type->parsed || rz_bin_pdb_type_is_fwdref(type)) {
				return base_type->type ? rz_type_clone(base_type->type) : NULL;
			} else if (base_type->attrs != RZ_TYPE_TYPECLASS_INVALID) {
				RZ_LOG_INFO("%s : Redefining type %s.\n", __FUNCTION__, name);
			}
		}
	}

	if (!base_type) {
		base_type = rz_type_base_type_new(RZ_BASE_TYPE_KIND_ENUM);
		if (!base_type) {
			return NULL;
		}

		RzPdbTpiType *utype = rz_bin_pdb_get_type_by_index(stream, lf_enum->utype);
		if (!utype) {
			rz_type_base_type_free(base_type);
			return NULL;
		}
		RzType *btype = pdb_type_parse(typedb, stream, utype, NULL);
		if (!btype) {
			rz_type_base_type_free(base_type);
			return NULL;
		}
		base_type->name = is_tpitype_unnamed(name) ? create_type_name_from_offset(type->index) : rz_str_dup(name);
		base_type->size = rz_type_db_get_bitsize(typedb, btype);
		base_type->type = btype;
		base_type->attrs = RZ_TYPE_TYPECLASS_INVALID;
		if (!rz_type_db_save_base_type(typedb, base_type)) {
			return NULL;
		}

		if (rz_bin_pdb_type_is_fwdref(type)) {
			return rz_type_clone(base_type->type);
		}
	}
	rz_vector_clear(&base_type->enum_data.cases);
	RzPVector *members = rz_bin_pdb_get_type_members(stream, type);
	void **it;
foreach_members:
	rz_pvector_foreach (members, it) {
		RzPdbTpiType *member_info = *it;
		PDB_PROCESS_LF_INDEX;
		RzTypeEnumCase *enum_case = enumerate_parse(member_info);
		if (!enum_case) {
			continue; // skip it, move forward
		}
		void *element = rz_vector_push(&base_type->enum_data.cases, enum_case);
		if (!element) {
			rz_type_base_enum_case_free(enum_case, NULL);
			return NULL;
		}
		free(enum_case);
	}
	if (base_type->attrs == RZ_TYPE_TYPECLASS_INVALID) {
		base_type->attrs = RZ_TYPE_TYPECLASS_NONE;
		rz_list_append(stream->print_type, base_type);
	}
	type->parsed = true;
	return base_type->type ? rz_type_clone(base_type->type) : NULL;
}

static RzType *pdb_type_parse_kind(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type, char *name) {
	switch (type->kind) {
	case TpiKind_SIMPLE_TYPE:
		return pdb_simple_type_parse(typedb, type);
	case TpiKind_CLASS:
		return class_parse(typedb, stream, type);
	case TpiKind_UNION:
		return union_parse(typedb, stream, type);
	case TpiKind_ENUM:
		return enum_parse(typedb, stream, type);
	case TpiKind_MODIFIER:
		return modifier_parse(typedb, stream, type);
	case TpiKind_ARRAY:
		return array_parse(typedb, stream, type);
	case TpiKind_POINTER:
		return pointer_parse(typedb, stream, type, name);
	case TpiKind_PROCEDURE:
		return procedure_parse(typedb, stream, type, name);
	case TpiKind_MFUNCTION:
		return mfunction_parse(typedb, stream, type, name);
	case TpiKind_BITFIELD:
	case TpiKind_BCLASS:
	case TpiKind_FILEDLIST:
	case TpiKind_ENUMERATE:
	case TpiKind_ARGLIST:
	case TpiKind_METHODLIST:
	case TpiKind_VTSHAPE:
	case TpiKind_VFTABLE:
	case TpiKind_LABEL:
	case TpiKind_NESTTYPE:
	case TpiKind_MEMBER:
	case TpiKind_METHOD:
	case TpiKind_ONEMETHOD:
	case TpiKind_VFUNCTAB:
	case TpiKind_STMEMBER:
	case TpiKind_VBCLASS:
	case TpiKind_INDEX:
		return NULL;
	default:
		rz_warn_if_reached();
		RZ_LOG_DEBUG("Unknown type record: #0x%" PFMT32x ": leaf=0x%" PFMT32x "\n",
			type->index, type->leaf);
		break;
	}
	return NULL;
}

static RzType *pdb_type_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type, char *name) {
	if (type->parsing) {
		// Stops at a type that refers to itself, because a broken or hostile PDB file can have one.
		return NULL;
	}
	type->parsing = true;
	RzType *result = pdb_type_parse_kind(typedb, stream, type, name);
	type->parsing = false;
	return result;
}

/**
 * \brief Delegate the type parsing to appropriate function
 *
 * \param t RzTypeDB instance
 * \param stream TPI Stream
 * \param type Current type
 */
RZ_API RzType *rz_type_db_pdb_parse(const RzTypeDB *typedb, RzPdbTpiStream *stream, RzPdbTpiType *type) {
	rz_return_val_if_fail(typedb && type, NULL);
	return pdb_type_parse(typedb, stream, type, NULL);
}

/**
 * \brief Saves PDB types from TPI stream into the type database
 *
 * \param t RzTypeDB instance
 * \param pdb PDB instance
 */
RZ_API void rz_type_db_pdb_load(const RzTypeDB *typedb, const RzPdb *pdb) {
	rz_return_if_fail(typedb && pdb);
	RzPdbTpiStream *stream = pdb->s_tpi;
	if (!stream) { // no TPI stream found
		return;
	}

	stream->print_type = rz_list_new();
	if (!stream->print_type) {
		return;
	}

	RBIter it;
	RzPdbTpiType *type;
	rz_rbtree_foreach (stream->types, it, type, RzPdbTpiType, rb) {
		if (type && is_parsable_type(type)) {
			rz_type_db_pdb_parse(typedb, stream, type);
		}
	}
}

// Register numbers of CodeView (cvconst.h) for the stack and frame pointers of x86 and x86-64
#define CV_REG_ESP       21
#define CV_REG_EBP       22
#define CV_AMD64_RBP     334
#define CV_AMD64_RSP     335
#define CV_ALLREG_VFRAME 30006

// Stops at this number of locals of a procedure, because each local costs a walk over the variables of the function.
#define PDB_MAX_LOCALS 1024

typedef struct {
	RzAnalysis *analysis;
	RzAnalysisFunction *fcn;
	const RzPdb *pdb;
	const PDBSFrameProcedure *frame;
	RzPVector /*<char *>*/ param_names;
	size_t param_count;
	size_t local_count;
} PdbFunction;

/**
 * \brief Returns a copy of the type of a procedure, with `this` as the first parameter of a method, or NULL
 *
 * Sets \p stored to the type in the type database, which has the name and address of the procedure, because overloads
 * and static functions of different files can have the same name.
 */
static RzCallable *pdb_procedure_callable(PdbFunction *ctx, const PDBSProcedure *procedure, RzCallable **stored) {
	RzPdbTpiStream *stream = ctx->pdb->s_tpi;
	PDBTypeIndex index = procedure->id ? rz_bin_pdb_get_function_type_by_id(ctx->pdb, procedure->type_index) : procedure->type_index;
	RzPdbTpiType *type = stream ? rz_bin_pdb_get_type_by_index(stream, index) : NULL;
	if (!type || (type->kind != TpiKind_PROCEDURE && type->kind != TpiKind_MFUNCTION) || RZ_STR_ISEMPTY(procedure->name)) {
		return NULL;
	}
	char *name = rz_str_newf("%s@0x%" PFMT64x, procedure->name, ctx->fcn->addr);
	RzType *parsed = name ? pdb_type_parse(ctx->analysis->typedb, stream, type, name) : NULL;
	free(name);
	*stored = parsed && parsed->kind == RZ_TYPE_KIND_CALLABLE ? parsed->callable : NULL;
	RzCallable *callable = *stored ? rz_type_callable_clone(*stored) : NULL;
	rz_type_free(parsed);
	if (!callable || type->kind != TpiKind_MFUNCTION) {
		return callable;
	}

	Tpi_LF_MFcuntion *method = type->data;
	RzPdbTpiType *this_type = rz_bin_pdb_get_type_by_index(stream, method->this_type);
	RzType *this_parsed = this_type ? pdb_type_parse(ctx->analysis->typedb, stream, this_type, NULL) : NULL;
	RzCallableArg *this_arg = this_parsed ? rz_type_callable_arg_new(ctx->analysis->typedb, "this", this_parsed) : NULL;
	if (this_arg) {
		rz_pvector_insert(callable->args, 0, this_arg);
	}
	return callable;
}

/**
 * \brief Gives the parameters of a function type the names of the variables of a procedure, after the first \p skip
 */
static void pdb_callable_rename(RzCallable *callable, const RzPVector /*<char *>*/ *names, size_t skip) {
	for (size_t i = 0; i < rz_pvector_len(callable->args) && skip + i < rz_pvector_len(names); i++) {
		RzCallableArg *arg = rz_pvector_at(callable->args, i);
		const char *name = rz_pvector_at(names, skip + i);
		if (RZ_STR_ISNOTEMPTY(name)) {
			free(arg->name);
			arg->name = rz_str_dup(name);
		}
	}
}

/**
 * \brief Returns the calling convention of the analysis for the calling convention of a PDB file on x86, or NULL
 *
 * Every function of x86-64 has the calling convention __cdecl in a PDB file, which is the one of the analysis.
 */
static const char *pdb_calling_convention(RzAnalysis *analysis, const char *cc) {
	static const char *const conventions[][2] = {
		{ "__cdecl", "cdecl" },
		{ "__stdcall", "stdcall" },
		{ "__fastcall", "fastcall" },
		{ "__thiscall", "cdecl-thiscall-ms" },
		{ "__pascal", "pascal" },
	};
	if (!cc || analysis->bits != 32 || !rz_analysis_is_cpu(analysis, "x86")) {
		return NULL;
	}
	for (size_t i = 0; i < RZ_ARRAY_SIZE(conventions); i++) {
		if (!strcmp(cc, conventions[i][0]) && rz_analysis_cc_exist(analysis, conventions[i][1])) {
			return conventions[i][1];
		}
	}
	return NULL;
}

/**
 * \brief Converts an offset from a CodeView register to an offset from the stack pointer at the entry of the function
 */
static bool pdb_stack_offset(PdbFunction *ctx, ut16 reg, st32 offset, RzStackAddr *result) {
	switch (reg) {
	case CV_ALLREG_VFRAME:
		// Keeps the offset, because the virtual frame of x86 starts at the return address.
		*result = offset;
		return true;
	case CV_REG_ESP:
	case CV_AMD64_RSP:
		// Subtracts the saved registers and the locals, because the stack pointer stays below both after the prologue.
		if (!ctx->frame) {
			return false;
		}
		*result = (st64)offset - ctx->frame->frame_size - ctx->frame->saved_registers_size;
		return true;
	case CV_REG_EBP:
	case CV_AMD64_RBP:
		*result = (st64)offset - ctx->fcn->bp_off;
		return true;
	default:
		return false;
	}
}

/**
 * \brief Returns the register of the S_DEFRANGE_FRAMEPOINTER_REL ranges of the procedure, or 0
 */
static ut16 pdb_frame_register(PdbFunction *ctx) {
	bool x86 = ctx->analysis->bits == 32;
	switch (ctx->frame ? ctx->frame->local_base_pointer : 0) {
	case 1: return x86 ? CV_ALLREG_VFRAME : CV_AMD64_RSP;
	case 2: return x86 ? CV_REG_EBP : CV_AMD64_RBP;
	default: return 0;
	}
}

static void pdb_local_add(PdbFunction *ctx, PDBTypeIndex type_index, const char *name, ut16 reg, st32 offset) {
	RzAnalysisVarStorage storage;
	RzStackAddr stack_off = 0;
	if (RZ_STR_ISEMPTY(name) || ctx->local_count >= PDB_MAX_LOCALS || !pdb_stack_offset(ctx, reg, offset, &stack_off)) {
		return;
	}
	ctx->local_count++;
	rz_analysis_var_storage_init_stack(&storage, stack_off);
	RzPdbTpiType *tpi_type = ctx->pdb->s_tpi ? rz_bin_pdb_get_type_by_index(ctx->pdb->s_tpi, type_index) : NULL;
	RzType *type = tpi_type ? pdb_type_parse(ctx->analysis->typedb, ctx->pdb->s_tpi, tpi_type, NULL) : NULL;
	RzAnalysisVar *var = rz_analysis_function_set_var(ctx->fcn, &storage, type, 0, name);
	if (var) {
		var->kind = RZ_ANALYSIS_VAR_KIND_VARIABLE;
		var->origin.kind = RZ_ANALYSIS_VAR_ORIGIN_PDB;
	}
	rz_type_free(type);
}

/**
 * \brief Takes a variable without a parameter flag as the next parameter until the procedure has all its parameters,
 * because the compiler of Microsoft writes the parameters first and doesn't mark them.
 */
static bool pdb_is_param(PdbFunction *ctx, const char *name) {
	void **it;
	rz_pvector_foreach (&ctx->param_names, it) {
		if (name && *it && !strcmp(name, *it)) {
			return true;
		}
	}
	return false;
}

static bool pdb_param_add(PdbFunction *ctx, const char *name) {
	if (rz_pvector_len(&ctx->param_names) >= ctx->param_count) {
		return false;
	}
	rz_pvector_push(&ctx->param_names, (void *)name);
	return true;
}

/**
 * \brief Adds the parameters, locals and type of the PDB procedure at the address of a function to the function
 *
 * Takes the names of the parameters from the variables of the procedure and their types from its type. Adds the locals
 * on the stack with their names and types. Skips the variables of inlined functions and of registers.
 *
 * \param analysis RzAnalysis instance
 * \param pdb PDB instance
 * \param baddr Base address of the binary of the PDB file
 * \param fcn Function to update
 * \return true if the PDB file has a procedure at the address of \p fcn
 */
RZ_API bool rz_analysis_pdb_integrate_function(RZ_NONNULL RzAnalysis *analysis, RZ_NONNULL const RzPdb *pdb, ut64 baddr,
	RZ_NONNULL RzAnalysisFunction *fcn) {
	rz_return_val_if_fail(analysis && pdb && fcn, false);
	const PDBProcedureEntry *entry = fcn->addr >= baddr ? rz_bin_pdb_get_procedure_at(pdb, fcn->addr - baddr) : NULL;
	if (!entry) {
		return false;
	}
	const RzPVector *symbols = entry->module->symbols;
	const PDBSProcedure *procedure = ((const PDBSymbol *)rz_pvector_at(symbols, entry->index))->data;

	// Finds the frame first, because the compiler of Microsoft can write it after the variables that need it.
	PdbFunction ctx = { .analysis = analysis, .fcn = fcn, .pdb = pdb };
	for (size_t i = entry->index + 1; i < rz_pvector_len(symbols) && !ctx.frame; i++) {
		const PDBSymbol *symbol = rz_pvector_at(symbols, i);
		if (symbol->index >= procedure->end) {
			break;
		}
		ctx.frame = symbol->kind == PDB_FrameProcedure ? symbol->data : NULL;
	}
	rz_pvector_init(&ctx.param_names, NULL);
	RzCallable *stored = NULL;
	RzCallable *callable = pdb_procedure_callable(&ctx, procedure, &stored);
	ctx.param_count = callable ? rz_pvector_len(callable->args) : 0;
	const PDBSLocal *local = NULL;
	ut32 inline_end = 0;
	for (size_t i = entry->index + 1; i < rz_pvector_len(symbols); i++) {
		const PDBSymbol *symbol = rz_pvector_at(symbols, i);
		if (symbol->index >= procedure->end) {
			break;
		}
		if (symbol->index < inline_end) {
			continue;
		}

		const void *data = symbol->data;
		const PDBSDefRange *range = data;
		const PDBSRegisterRelative *relative = data;
		switch (symbol->kind) {
		case PDB_InlineSite:
			inline_end = ((const PDBSInlineSite *)data)->end;
			break;
		case PDB_Local:
			local = data;
			if (local->param) {
				rz_pvector_push(&ctx.param_names, local->name);
			}
			if (local->param || local->optimized_out) {
				local = NULL;
			}
			break;
		case PDB_DefRangeFramePointerRelative:
		case PDB_DefRangeFramePointerRelativeFullScope:
		case PDB_DefRangeRegisterRelative:
			if (local) {
				ut16 reg = symbol->kind == PDB_DefRangeRegisterRelative ? range->register_index : pdb_frame_register(&ctx);
				pdb_local_add(&ctx, local->type_index, local->name, reg, range->offset);
				local = NULL;
			}
			break;
		case PDB_RegisterRelative:
		case PDB_BasePointerRelative:
			// Skips the home slot of a parameter that a S_LOCAL already gave a name, because the parameter keeps its
			// place in the calling convention.
			if (!pdb_is_param(&ctx, relative->name) && !pdb_param_add(&ctx, relative->name)) {
				ut16 reg = symbol->kind == PDB_RegisterRelative ? relative->register_index : CV_REG_EBP;
				pdb_local_add(&ctx, relative->type_index, relative->name, reg, relative->offset);
			}
			break;
		case PDB_RegisterVariable:
			pdb_param_add(&ctx, ((const PDBSRegisterVariable *)data)->name);
			break;
		default:
			break;
		}
	}

	if (callable) {
		pdb_callable_rename(callable, &ctx.param_names, 0);
		pdb_callable_rename(stored, &ctx.param_names, rz_pvector_len(callable->args) - rz_pvector_len(stored->args));
		callable->cc = pdb_calling_convention(analysis, callable->cc);
		rz_analysis_function_set_type(analysis, fcn, callable);
		void **it;
		rz_pvector_foreach (callable->args, it) {
			RzAnalysisVar *var = rz_analysis_function_get_var_byname(fcn, ((RzCallableArg *)*it)->name);
			if (var) {
				var->kind = RZ_ANALYSIS_VAR_KIND_FORMAL_PARAMETER;
				var->origin.kind = RZ_ANALYSIS_VAR_ORIGIN_PDB;
			}
		}
		rz_type_callable_free(callable);
	}
	rz_pvector_fini(&ctx.param_names);
	fcn->has_debuginfo = true;
	return true;
}
