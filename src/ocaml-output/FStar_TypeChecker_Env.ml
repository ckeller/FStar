open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv
  | Binding_lid of (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
  FStar_Pervasives_Native.tuple2
  | Binding_sig of (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
  FStar_Pervasives_Native.tuple2
  | Binding_univ of FStar_Syntax_Syntax.univ_name
  | Binding_sig_inst of
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
  FStar_Pervasives_Native.tuple3
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____44 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____62 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____94 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____126 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____148 -> false
let __proj__Binding_sig_inst__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
  | UnfoldTac
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____189 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____194 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____199 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____205 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____218 -> false
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option;}
let __proj__Mkmlift__item__mlift_wp:
  mlift ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let __proj__Mkmlift__item__mlift_term:
  mlift ->
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
type edge =
  {
  msource: FStar_Ident.lident;
  mtarget: FStar_Ident.lident;
  mlift: mlift;}
let __proj__Mkedge__item__msource: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
let __proj__Mkedge__item__mtarget: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
let __proj__Mkedge__item__mlift: edge -> mlift =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list;}
let __proj__Mkeffects__item__decls:
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
let __proj__Mkeffects__item__order: effects -> edge Prims.list =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
let __proj__Mkeffects__item__joins:
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
type name_prefix = Prims.string Prims.list
type flat_proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
type proof_namespace = flat_proof_namespace Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t;
  range: FStar_Range.range;
  curmodule: FStar_Ident.lident;
  gamma: binding Prims.list;
  gamma_cache: cached_elt FStar_Util.smap;
  modules: FStar_Syntax_Syntax.modul Prims.list;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap;
  is_pattern: Prims.bool;
  instantiate_imp: Prims.bool;
  effects: effects;
  generalize: Prims.bool;
  letrecs:
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  top_level: Prims.bool;
  check_uvars: Prims.bool;
  use_eq: Prims.bool;
  is_iface: Prims.bool;
  admit: Prims.bool;
  lax: Prims.bool;
  lax_universes: Prims.bool;
  failhard: Prims.bool;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe;
  use_bv_sorts: Prims.bool;
  qname_and_index:
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option;
  proof_ns: proof_namespace;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term;
  is_native_tactic: FStar_Ident.lid -> Prims.bool;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref;
  tc_hooks: tcenv_hooks;}
and solver_t =
  {
  init: env -> Prims.unit;
  push: Prims.string -> Prims.unit;
  pop: Prims.string -> Prims.unit;
  mark: Prims.string -> Prims.unit;
  reset_mark: Prims.string -> Prims.unit;
  commit_mark: Prims.string -> Prims.unit;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list;
  solve:
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool;
  finish: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;}
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula;
  deferred: FStar_TypeChecker_Common.deferred;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2;
  implicits:
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list;}
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> Prims.unit;}
let __proj__Mkenv__item__solver: env -> solver_t =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__solver
let __proj__Mkenv__item__range: env -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__range
let __proj__Mkenv__item__curmodule: env -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__curmodule
let __proj__Mkenv__item__gamma: env -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__gamma
let __proj__Mkenv__item__gamma_cache: env -> cached_elt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__gamma_cache
let __proj__Mkenv__item__modules: env -> FStar_Syntax_Syntax.modul Prims.list
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__modules
let __proj__Mkenv__item__expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__expected_typ
let __proj__Mkenv__item__sigtab:
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__sigtab
let __proj__Mkenv__item__is_pattern: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_pattern
let __proj__Mkenv__item__instantiate_imp: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__instantiate_imp
let __proj__Mkenv__item__effects: env -> effects =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__effects
let __proj__Mkenv__item__generalize: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__generalize
let __proj__Mkenv__item__letrecs:
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__letrecs
let __proj__Mkenv__item__top_level: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__top_level
let __proj__Mkenv__item__check_uvars: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__check_uvars
let __proj__Mkenv__item__use_eq: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__use_eq
let __proj__Mkenv__item__is_iface: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_iface
let __proj__Mkenv__item__admit: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__admit
let __proj__Mkenv__item__lax: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__lax
let __proj__Mkenv__item__lax_universes: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__lax_universes
let __proj__Mkenv__item__failhard: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__failhard
let __proj__Mkenv__item__type_of:
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__type_of
let __proj__Mkenv__item__universe_of:
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__universe_of
let __proj__Mkenv__item__use_bv_sorts: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__use_bv_sorts
let __proj__Mkenv__item__qname_and_index:
  env ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__qname_and_index
let __proj__Mkenv__item__proof_ns: env -> proof_namespace =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__proof_ns
let __proj__Mkenv__item__synth:
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__synth
let __proj__Mkenv__item__is_native_tactic:
  env -> FStar_Ident.lid -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_native_tactic
let __proj__Mkenv__item__identifier_info:
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__identifier_info
let __proj__Mkenv__item__tc_hooks: env -> tcenv_hooks =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__tc_hooks
let __proj__Mksolver_t__item__init: solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__init
let __proj__Mksolver_t__item__push: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__push
let __proj__Mksolver_t__item__pop: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__pop
let __proj__Mksolver_t__item__mark: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__mark
let __proj__Mksolver_t__item__reset_mark:
  solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__reset_mark
let __proj__Mksolver_t__item__commit_mark:
  solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__commit_mark
let __proj__Mksolver_t__item__encode_modul:
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_modul
let __proj__Mksolver_t__item__encode_sig:
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_sig
let __proj__Mksolver_t__item__preprocess:
  solver_t ->
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__preprocess
let __proj__Mksolver_t__item__solve:
  solver_t ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__solve
let __proj__Mksolver_t__item__is_trivial:
  solver_t -> env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__is_trivial
let __proj__Mksolver_t__item__finish: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__finish
let __proj__Mksolver_t__item__refresh: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__refresh
let __proj__Mkguard_t__item__guard_f:
  guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
let __proj__Mkguard_t__item__deferred:
  guard_t -> FStar_TypeChecker_Common.deferred =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
let __proj__Mkguard_t__item__univ_ineqs:
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
let __proj__Mkguard_t__item__implicits:
  guard_t ->
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook:
  tcenv_hooks -> env -> binding -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4652  -> fun uu____4653  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___122_4666 = env in
      {
        solver = (uu___122_4666.solver);
        range = (uu___122_4666.range);
        curmodule = (uu___122_4666.curmodule);
        gamma = (uu___122_4666.gamma);
        gamma_cache = (uu___122_4666.gamma_cache);
        modules = (uu___122_4666.modules);
        expected_typ = (uu___122_4666.expected_typ);
        sigtab = (uu___122_4666.sigtab);
        is_pattern = (uu___122_4666.is_pattern);
        instantiate_imp = (uu___122_4666.instantiate_imp);
        effects = (uu___122_4666.effects);
        generalize = (uu___122_4666.generalize);
        letrecs = (uu___122_4666.letrecs);
        top_level = (uu___122_4666.top_level);
        check_uvars = (uu___122_4666.check_uvars);
        use_eq = (uu___122_4666.use_eq);
        is_iface = (uu___122_4666.is_iface);
        admit = (uu___122_4666.admit);
        lax = (uu___122_4666.lax);
        lax_universes = (uu___122_4666.lax_universes);
        failhard = (uu___122_4666.failhard);
        type_of = (uu___122_4666.type_of);
        universe_of = (uu___122_4666.universe_of);
        use_bv_sorts = (uu___122_4666.use_bv_sorts);
        qname_and_index = (uu___122_4666.qname_and_index);
        proof_ns = (uu___122_4666.proof_ns);
        synth = (uu___122_4666.synth);
        is_native_tactic = (uu___122_4666.is_native_tactic);
        identifier_info = (uu___122_4666.identifier_info);
        tc_hooks = hooks
      }
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let should_verify: env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let visible_at: delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____4681) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4682,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4683,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4684 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4693 . Prims.unit -> 'Auu____4693 FStar_Util.smap =
  fun uu____4699  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4704 . Prims.unit -> 'Auu____4704 FStar_Util.smap =
  fun uu____4710  -> FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
         FStar_Pervasives_Native.tuple3)
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____4759 = new_gamma_cache () in
          let uu____4762 = new_sigtab () in
          let uu____4765 =
            let uu____4766 = FStar_Options.using_facts_from () in
            match uu____4766 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____4776 =
                  let uu____4785 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____4785 [([], false)] in
                [uu____4776]
            | FStar_Pervasives_Native.None  -> [[]] in
          let uu____4858 =
            FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____4759;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____4762;
            is_pattern = false;
            instantiate_imp = true;
            effects = { decls = []; order = []; joins = [] };
            generalize = true;
            letrecs = [];
            top_level = false;
            check_uvars = false;
            use_eq = false;
            is_iface = false;
            admit = false;
            lax = false;
            lax_universes = false;
            failhard = false;
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = FStar_Pervasives_Native.None;
            proof_ns = uu____4765;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____4892  -> false);
            identifier_info = uu____4858;
            tc_hooks = default_tc_hooks
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref
  = FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____4963  ->
    let uu____4964 = FStar_ST.op_Bang query_indices in
    match uu____4964 with
    | [] -> failwith "Empty query indices!"
    | uu____5021 ->
        let uu____5030 =
          let uu____5039 =
            let uu____5046 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5046 in
          let uu____5103 = FStar_ST.op_Bang query_indices in uu____5039 ::
            uu____5103 in
        FStar_ST.op_Colon_Equals query_indices uu____5030
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5205  ->
    let uu____5206 = FStar_ST.op_Bang query_indices in
    match uu____5206 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5334  ->
    match uu____5334 with
    | (l,n1) ->
        let uu____5341 = FStar_ST.op_Bang query_indices in
        (match uu____5341 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5466 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5484  ->
    let uu____5485 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5485
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____5545  ->
    let uu____5546 = FStar_ST.op_Bang query_indices in
    match uu____5546 with
    | hd1::uu____5598::tl1 ->
        FStar_ST.op_Colon_Equals query_indices (hd1 :: tl1)
    | uu____5680 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5707 =
       let uu____5710 = FStar_ST.op_Bang stack in env :: uu____5710 in
     FStar_ST.op_Colon_Equals stack uu____5707);
    (let uu___123_5749 = env in
     let uu____5750 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5753 = FStar_Util.smap_copy (sigtab env) in
     let uu____5756 =
       let uu____5759 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5759 in
     {
       solver = (uu___123_5749.solver);
       range = (uu___123_5749.range);
       curmodule = (uu___123_5749.curmodule);
       gamma = (uu___123_5749.gamma);
       gamma_cache = uu____5750;
       modules = (uu___123_5749.modules);
       expected_typ = (uu___123_5749.expected_typ);
       sigtab = uu____5753;
       is_pattern = (uu___123_5749.is_pattern);
       instantiate_imp = (uu___123_5749.instantiate_imp);
       effects = (uu___123_5749.effects);
       generalize = (uu___123_5749.generalize);
       letrecs = (uu___123_5749.letrecs);
       top_level = (uu___123_5749.top_level);
       check_uvars = (uu___123_5749.check_uvars);
       use_eq = (uu___123_5749.use_eq);
       is_iface = (uu___123_5749.is_iface);
       admit = (uu___123_5749.admit);
       lax = (uu___123_5749.lax);
       lax_universes = (uu___123_5749.lax_universes);
       failhard = (uu___123_5749.failhard);
       type_of = (uu___123_5749.type_of);
       universe_of = (uu___123_5749.universe_of);
       use_bv_sorts = (uu___123_5749.use_bv_sorts);
       qname_and_index = (uu___123_5749.qname_and_index);
       proof_ns = (uu___123_5749.proof_ns);
       synth = (uu___123_5749.synth);
       is_native_tactic = (uu___123_5749.is_native_tactic);
       identifier_info = uu____5756;
       tc_hooks = (uu___123_5749.tc_hooks)
     })
let pop_stack: Prims.unit -> env =
  fun uu____5787  ->
    let uu____5788 = FStar_ST.op_Bang stack in
    match uu____5788 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____5832 -> failwith "Impossible: Too many pops"
let cleanup_interactive: env -> Prims.unit = fun env  -> (env.solver).pop ""
let push: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
let pop: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let mark: env -> env =
  fun env  ->
    (env.solver).mark "USER MARK"; push_query_indices (); push_stack env
let commit_mark: env -> env =
  fun env  ->
    commit_query_index_mark ();
    (env.solver).commit_mark "USER MARK";
    (let uu____5872 = pop_stack () in ());
    env
let reset_mark: env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
let incr_query_index: env -> env =
  fun env  ->
    let qix = peek_query_indices () in
    match env.qname_and_index with
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____5900 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____5926  ->
                  match uu____5926 with
                  | (m,uu____5932) -> FStar_Ident.lid_equals l m)) in
        (match uu____5900 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___124_5939 = env in
               {
                 solver = (uu___124_5939.solver);
                 range = (uu___124_5939.range);
                 curmodule = (uu___124_5939.curmodule);
                 gamma = (uu___124_5939.gamma);
                 gamma_cache = (uu___124_5939.gamma_cache);
                 modules = (uu___124_5939.modules);
                 expected_typ = (uu___124_5939.expected_typ);
                 sigtab = (uu___124_5939.sigtab);
                 is_pattern = (uu___124_5939.is_pattern);
                 instantiate_imp = (uu___124_5939.instantiate_imp);
                 effects = (uu___124_5939.effects);
                 generalize = (uu___124_5939.generalize);
                 letrecs = (uu___124_5939.letrecs);
                 top_level = (uu___124_5939.top_level);
                 check_uvars = (uu___124_5939.check_uvars);
                 use_eq = (uu___124_5939.use_eq);
                 is_iface = (uu___124_5939.is_iface);
                 admit = (uu___124_5939.admit);
                 lax = (uu___124_5939.lax);
                 lax_universes = (uu___124_5939.lax_universes);
                 failhard = (uu___124_5939.failhard);
                 type_of = (uu___124_5939.type_of);
                 universe_of = (uu___124_5939.universe_of);
                 use_bv_sorts = (uu___124_5939.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___124_5939.proof_ns);
                 synth = (uu___124_5939.synth);
                 is_native_tactic = (uu___124_5939.is_native_tactic);
                 identifier_info = (uu___124_5939.identifier_info);
                 tc_hooks = (uu___124_5939.tc_hooks)
               }))
         | FStar_Pervasives_Native.Some (uu____5944,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___125_5952 = env in
               {
                 solver = (uu___125_5952.solver);
                 range = (uu___125_5952.range);
                 curmodule = (uu___125_5952.curmodule);
                 gamma = (uu___125_5952.gamma);
                 gamma_cache = (uu___125_5952.gamma_cache);
                 modules = (uu___125_5952.modules);
                 expected_typ = (uu___125_5952.expected_typ);
                 sigtab = (uu___125_5952.sigtab);
                 is_pattern = (uu___125_5952.is_pattern);
                 instantiate_imp = (uu___125_5952.instantiate_imp);
                 effects = (uu___125_5952.effects);
                 generalize = (uu___125_5952.generalize);
                 letrecs = (uu___125_5952.letrecs);
                 top_level = (uu___125_5952.top_level);
                 check_uvars = (uu___125_5952.check_uvars);
                 use_eq = (uu___125_5952.use_eq);
                 is_iface = (uu___125_5952.is_iface);
                 admit = (uu___125_5952.admit);
                 lax = (uu___125_5952.lax);
                 lax_universes = (uu___125_5952.lax_universes);
                 failhard = (uu___125_5952.failhard);
                 type_of = (uu___125_5952.type_of);
                 universe_of = (uu___125_5952.universe_of);
                 use_bv_sorts = (uu___125_5952.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___125_5952.proof_ns);
                 synth = (uu___125_5952.synth);
                 is_native_tactic = (uu___125_5952.is_native_tactic);
                 identifier_info = (uu___125_5952.identifier_info);
                 tc_hooks = (uu___125_5952.tc_hooks)
               })))
let debug: env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let set_range: env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___126_5974 = e in
         {
           solver = (uu___126_5974.solver);
           range = r;
           curmodule = (uu___126_5974.curmodule);
           gamma = (uu___126_5974.gamma);
           gamma_cache = (uu___126_5974.gamma_cache);
           modules = (uu___126_5974.modules);
           expected_typ = (uu___126_5974.expected_typ);
           sigtab = (uu___126_5974.sigtab);
           is_pattern = (uu___126_5974.is_pattern);
           instantiate_imp = (uu___126_5974.instantiate_imp);
           effects = (uu___126_5974.effects);
           generalize = (uu___126_5974.generalize);
           letrecs = (uu___126_5974.letrecs);
           top_level = (uu___126_5974.top_level);
           check_uvars = (uu___126_5974.check_uvars);
           use_eq = (uu___126_5974.use_eq);
           is_iface = (uu___126_5974.is_iface);
           admit = (uu___126_5974.admit);
           lax = (uu___126_5974.lax);
           lax_universes = (uu___126_5974.lax_universes);
           failhard = (uu___126_5974.failhard);
           type_of = (uu___126_5974.type_of);
           universe_of = (uu___126_5974.universe_of);
           use_bv_sorts = (uu___126_5974.use_bv_sorts);
           qname_and_index = (uu___126_5974.qname_and_index);
           proof_ns = (uu___126_5974.proof_ns);
           synth = (uu___126_5974.synth);
           is_native_tactic = (uu___126_5974.is_native_tactic);
           identifier_info = (uu___126_5974.identifier_info);
           tc_hooks = (uu___126_5974.tc_hooks)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____5987 =
        let uu____5988 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____5988 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5987
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6021 =
          let uu____6022 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6022 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6021
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6055 =
          let uu____6056 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6056 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6055
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6090 =
        let uu____6091 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6091 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6090
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___127_6130 = env in
      {
        solver = (uu___127_6130.solver);
        range = (uu___127_6130.range);
        curmodule = lid;
        gamma = (uu___127_6130.gamma);
        gamma_cache = (uu___127_6130.gamma_cache);
        modules = (uu___127_6130.modules);
        expected_typ = (uu___127_6130.expected_typ);
        sigtab = (uu___127_6130.sigtab);
        is_pattern = (uu___127_6130.is_pattern);
        instantiate_imp = (uu___127_6130.instantiate_imp);
        effects = (uu___127_6130.effects);
        generalize = (uu___127_6130.generalize);
        letrecs = (uu___127_6130.letrecs);
        top_level = (uu___127_6130.top_level);
        check_uvars = (uu___127_6130.check_uvars);
        use_eq = (uu___127_6130.use_eq);
        is_iface = (uu___127_6130.is_iface);
        admit = (uu___127_6130.admit);
        lax = (uu___127_6130.lax);
        lax_universes = (uu___127_6130.lax_universes);
        failhard = (uu___127_6130.failhard);
        type_of = (uu___127_6130.type_of);
        universe_of = (uu___127_6130.universe_of);
        use_bv_sorts = (uu___127_6130.use_bv_sorts);
        qname_and_index = (uu___127_6130.qname_and_index);
        proof_ns = (uu___127_6130.proof_ns);
        synth = (uu___127_6130.synth);
        is_native_tactic = (uu___127_6130.is_native_tactic);
        identifier_info = (uu___127_6130.identifier_info);
        tc_hooks = (uu___127_6130.tc_hooks)
      }
let has_interface: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let find_in_sigtab:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
let name_not_found: FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str
let variable_not_found: FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____6161 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6161
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6165  ->
    let uu____6166 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6166
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____6206) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6230 = FStar_Syntax_Subst.subst vs t in (us, uu____6230)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___110_6244  ->
    match uu___110_6244 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6268  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6283 = inst_tscheme t in
      match uu____6283 with
      | (us,t1) ->
          let uu____6294 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6294)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6310  ->
          match uu____6310 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6325 =
                         let uu____6326 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6327 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6328 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6329 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6326 uu____6327 uu____6328 uu____6329 in
                       failwith uu____6325)
                    else ();
                    (let uu____6331 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6331))
               | uu____6338 ->
                   let uu____6339 =
                     let uu____6340 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6340 in
                   failwith uu____6339)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6345 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6350 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6355 -> false
let in_cur_mod: env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
      let cur = current_module env in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident] in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident] in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____6391) -> Maybe
             | (uu____6398,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6417 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                           FStar_Syntax_Syntax.universes
                                             FStar_Pervasives_Native.option)
                                           FStar_Pervasives_Native.tuple2)
         FStar_Util.either,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____6524 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____6524 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___111_6569  ->
                   match uu___111_6569 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____6612 =
                           let uu____6631 =
                             let uu____6646 = inst_tscheme t in
                             FStar_Util.Inl uu____6646 in
                           (uu____6631, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____6612
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____6712,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____6714);
                                     FStar_Syntax_Syntax.sigrng = uu____6715;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____6716;
                                     FStar_Syntax_Syntax.sigmeta = uu____6717;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____6718;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____6738 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____6738
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____6784 ->
                             FStar_Pervasives_Native.Some t
                         | uu____6791 -> cache t in
                       let uu____6792 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6792 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____6867 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6867 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____6953 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7033 = find_in_sigtab env lid in
         match uu____7033 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7132) ->
          add_sigelts env ses
      | uu____7141 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____7155 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___112_7184  ->
           match uu___112_7184 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7202 -> FStar_Pervasives_Native.None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let ((uu____7237,lb::[]),uu____7239) ->
          let uu____7252 =
            let uu____7261 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7270 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7261, uu____7270) in
          FStar_Pervasives_Native.Some uu____7252
      | FStar_Syntax_Syntax.Sig_let ((uu____7283,lbs),uu____7285) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7321 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7333 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7333
                   then
                     let uu____7344 =
                       let uu____7353 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7362 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7353, uu____7362) in
                     FStar_Pervasives_Native.Some uu____7344
                   else FStar_Pervasives_Native.None)
      | uu____7384 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7418 =
          let uu____7427 =
            let uu____7432 =
              let uu____7433 =
                let uu____7436 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7436 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7433) in
            inst_tscheme uu____7432 in
          (uu____7427, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7418
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7456,uu____7457) ->
        let uu____7462 =
          let uu____7471 =
            let uu____7476 =
              let uu____7477 =
                let uu____7480 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____7480 in
              (us, uu____7477) in
            inst_tscheme uu____7476 in
          (uu____7471, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7462
    | uu____7497 -> FStar_Pervasives_Native.None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                        FStar_Syntax_Syntax.syntax)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____7557 =
        match uu____7557 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____7653,uvs,t,uu____7656,uu____7657,uu____7658);
                    FStar_Syntax_Syntax.sigrng = uu____7659;
                    FStar_Syntax_Syntax.sigquals = uu____7660;
                    FStar_Syntax_Syntax.sigmeta = uu____7661;
                    FStar_Syntax_Syntax.sigattrs = uu____7662;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7683 =
                   let uu____7692 = inst_tscheme (uvs, t) in
                   (uu____7692, rng) in
                 FStar_Pervasives_Native.Some uu____7683
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____7712;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____7714;
                    FStar_Syntax_Syntax.sigattrs = uu____7715;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7732 =
                   let uu____7733 = in_cur_mod env l in uu____7733 = Yes in
                 if uu____7732
                 then
                   let uu____7744 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____7744
                    then
                      let uu____7757 =
                        let uu____7766 = inst_tscheme (uvs, t) in
                        (uu____7766, rng) in
                      FStar_Pervasives_Native.Some uu____7757
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____7793 =
                      let uu____7802 = inst_tscheme (uvs, t) in
                      (uu____7802, rng) in
                    FStar_Pervasives_Native.Some uu____7793)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7823,uu____7824);
                    FStar_Syntax_Syntax.sigrng = uu____7825;
                    FStar_Syntax_Syntax.sigquals = uu____7826;
                    FStar_Syntax_Syntax.sigmeta = uu____7827;
                    FStar_Syntax_Syntax.sigattrs = uu____7828;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____7867 =
                        let uu____7876 = inst_tscheme (uvs, k) in
                        (uu____7876, rng) in
                      FStar_Pervasives_Native.Some uu____7867
                  | uu____7893 ->
                      let uu____7894 =
                        let uu____7903 =
                          let uu____7908 =
                            let uu____7909 =
                              let uu____7912 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7912 in
                            (uvs, uu____7909) in
                          inst_tscheme uu____7908 in
                        (uu____7903, rng) in
                      FStar_Pervasives_Native.Some uu____7894)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7933,uu____7934);
                    FStar_Syntax_Syntax.sigrng = uu____7935;
                    FStar_Syntax_Syntax.sigquals = uu____7936;
                    FStar_Syntax_Syntax.sigmeta = uu____7937;
                    FStar_Syntax_Syntax.sigattrs = uu____7938;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____7978 =
                        let uu____7987 = inst_tscheme_with (uvs, k) us in
                        (uu____7987, rng) in
                      FStar_Pervasives_Native.Some uu____7978
                  | uu____8004 ->
                      let uu____8005 =
                        let uu____8014 =
                          let uu____8019 =
                            let uu____8020 =
                              let uu____8023 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8023 in
                            (uvs, uu____8020) in
                          inst_tscheme_with uu____8019 us in
                        (uu____8014, rng) in
                      FStar_Pervasives_Native.Some uu____8005)
             | FStar_Util.Inr se ->
                 let uu____8057 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8078;
                        FStar_Syntax_Syntax.sigrng = uu____8079;
                        FStar_Syntax_Syntax.sigquals = uu____8080;
                        FStar_Syntax_Syntax.sigmeta = uu____8081;
                        FStar_Syntax_Syntax.sigattrs = uu____8082;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8097 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8057
                   (FStar_Util.map_option
                      (fun uu____8145  ->
                         match uu____8145 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8176 =
        let uu____8187 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8187 mapper in
      match uu____8176 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___128_8280 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___128_8280.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___128_8280.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8307 = lookup_qname env l in
      match uu____8307 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8346 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8396 = try_lookup_bv env bv in
      match uu____8396 with
      | FStar_Pervasives_Native.None  ->
          let uu____8411 =
            let uu____8412 =
              let uu____8417 = variable_not_found bv in (uu____8417, bvr) in
            FStar_Errors.Error uu____8412 in
          FStar_Exn.raise uu____8411
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8428 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8429 = FStar_Range.set_use_range r bvr in
          (uu____8428, uu____8429)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8448 = try_lookup_lid_aux env l in
      match uu____8448 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____8514 =
            let uu____8523 =
              let uu____8528 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____8528) in
            (uu____8523, r1) in
          FStar_Pervasives_Native.Some uu____8514
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____8557 = try_lookup_lid env l in
      match uu____8557 with
      | FStar_Pervasives_Native.None  ->
          let uu____8584 =
            let uu____8585 =
              let uu____8590 = name_not_found l in
              (uu____8590, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____8585 in
          FStar_Exn.raise uu____8584
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___113_8628  ->
              match uu___113_8628 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____8630 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____8647 = lookup_qname env lid in
      match uu____8647 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8676,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8679;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8681;
              FStar_Syntax_Syntax.sigattrs = uu____8682;_},FStar_Pervasives_Native.None
            ),uu____8683)
          ->
          let uu____8732 =
            let uu____8743 =
              let uu____8748 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____8748) in
            (uu____8743, q) in
          FStar_Pervasives_Native.Some uu____8732
      | uu____8765 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8804 = lookup_qname env lid in
      match uu____8804 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8829,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8832;
              FStar_Syntax_Syntax.sigquals = uu____8833;
              FStar_Syntax_Syntax.sigmeta = uu____8834;
              FStar_Syntax_Syntax.sigattrs = uu____8835;_},FStar_Pervasives_Native.None
            ),uu____8836)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8885 ->
          let uu____8906 =
            let uu____8907 =
              let uu____8912 = name_not_found lid in
              (uu____8912, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8907 in
          FStar_Exn.raise uu____8906
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8929 = lookup_qname env lid in
      match uu____8929 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8954,uvs,t,uu____8957,uu____8958,uu____8959);
              FStar_Syntax_Syntax.sigrng = uu____8960;
              FStar_Syntax_Syntax.sigquals = uu____8961;
              FStar_Syntax_Syntax.sigmeta = uu____8962;
              FStar_Syntax_Syntax.sigattrs = uu____8963;_},FStar_Pervasives_Native.None
            ),uu____8964)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9017 ->
          let uu____9038 =
            let uu____9039 =
              let uu____9044 = name_not_found lid in
              (uu____9044, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9039 in
          FStar_Exn.raise uu____9038
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9063 = lookup_qname env lid in
      match uu____9063 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9090,uu____9091,uu____9092,uu____9093,uu____9094,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9096;
              FStar_Syntax_Syntax.sigquals = uu____9097;
              FStar_Syntax_Syntax.sigmeta = uu____9098;
              FStar_Syntax_Syntax.sigattrs = uu____9099;_},uu____9100),uu____9101)
          -> (true, dcs)
      | uu____9162 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9193 = lookup_qname env lid in
      match uu____9193 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9214,uu____9215,uu____9216,l,uu____9218,uu____9219);
              FStar_Syntax_Syntax.sigrng = uu____9220;
              FStar_Syntax_Syntax.sigquals = uu____9221;
              FStar_Syntax_Syntax.sigmeta = uu____9222;
              FStar_Syntax_Syntax.sigattrs = uu____9223;_},uu____9224),uu____9225)
          -> l
      | uu____9280 ->
          let uu____9301 =
            let uu____9302 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9302 in
          failwith uu____9301
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        let uu____9339 = lookup_qname env lid in
        match uu____9339 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9367) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9418,lbs),uu____9420) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9448 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9448
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9480 -> FStar_Pervasives_Native.None)
        | uu____9485 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____9522 = lookup_qname env ftv in
      match uu____9522 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9546) ->
          let uu____9591 = effect_signature se in
          (match uu____9591 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____9612,t),r) ->
               let uu____9627 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____9627)
      | uu____9628 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____9657 = try_lookup_effect_lid env ftv in
      match uu____9657 with
      | FStar_Pervasives_Native.None  ->
          let uu____9660 =
            let uu____9661 =
              let uu____9666 = name_not_found ftv in
              (uu____9666, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____9661 in
          FStar_Exn.raise uu____9660
      | FStar_Pervasives_Native.Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____9686 = lookup_qname env lid0 in
        match uu____9686 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____9717);
                FStar_Syntax_Syntax.sigrng = uu____9718;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____9720;
                FStar_Syntax_Syntax.sigattrs = uu____9721;_},FStar_Pervasives_Native.None
              ),uu____9722)
            ->
            let lid1 =
              let uu____9776 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____9776 in
            let uu____9777 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___114_9781  ->
                      match uu___114_9781 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9782 -> false)) in
            if uu____9777
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____9796 =
                      let uu____9797 =
                        let uu____9798 = get_range env in
                        FStar_Range.string_of_range uu____9798 in
                      let uu____9799 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____9800 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____9797 uu____9799 uu____9800 in
                    failwith uu____9796) in
               match (binders, univs1) with
               | ([],uu____9807) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____9824,uu____9825::uu____9826::uu____9827) ->
                   let uu____9832 =
                     let uu____9833 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____9834 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____9833 uu____9834 in
                   failwith uu____9832
               | uu____9841 ->
                   let uu____9846 =
                     let uu____9851 =
                       let uu____9852 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____9852) in
                     inst_tscheme_with uu____9851 insts in
                   (match uu____9846 with
                    | (uu____9863,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____9866 =
                          let uu____9867 = FStar_Syntax_Subst.compress t1 in
                          uu____9867.FStar_Syntax_Syntax.n in
                        (match uu____9866 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____9914 -> failwith "Impossible")))
        | uu____9921 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____9963 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____9963 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____9976,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____9983 = find1 l2 in
            (match uu____9983 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____9990 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____9990 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____9994 = find1 l in
            (match uu____9994 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10010 = lookup_qname env l1 in
      match uu____10010 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10033;
              FStar_Syntax_Syntax.sigrng = uu____10034;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10036;
              FStar_Syntax_Syntax.sigattrs = uu____10037;_},uu____10038),uu____10039)
          -> q
      | uu____10090 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10126 =
          let uu____10127 =
            let uu____10128 = FStar_Util.string_of_int i in
            let uu____10129 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10128 uu____10129 in
          failwith uu____10127 in
        let uu____10130 = lookup_datacon env lid in
        match uu____10130 with
        | (uu____10135,t) ->
            let uu____10137 =
              let uu____10138 = FStar_Syntax_Subst.compress t in
              uu____10138.FStar_Syntax_Syntax.n in
            (match uu____10137 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10142) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10173 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10173
                      FStar_Pervasives_Native.fst)
             | uu____10182 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10191 = lookup_qname env l in
      match uu____10191 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10212,uu____10213,uu____10214);
              FStar_Syntax_Syntax.sigrng = uu____10215;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10217;
              FStar_Syntax_Syntax.sigattrs = uu____10218;_},uu____10219),uu____10220)
          ->
          FStar_Util.for_some
            (fun uu___115_10273  ->
               match uu___115_10273 with
               | FStar_Syntax_Syntax.Projector uu____10274 -> true
               | uu____10279 -> false) quals
      | uu____10280 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10309 = lookup_qname env lid in
      match uu____10309 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10330,uu____10331,uu____10332,uu____10333,uu____10334,uu____10335);
              FStar_Syntax_Syntax.sigrng = uu____10336;
              FStar_Syntax_Syntax.sigquals = uu____10337;
              FStar_Syntax_Syntax.sigmeta = uu____10338;
              FStar_Syntax_Syntax.sigattrs = uu____10339;_},uu____10340),uu____10341)
          -> true
      | uu____10396 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10425 = lookup_qname env lid in
      match uu____10425 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10446,uu____10447,uu____10448,uu____10449,uu____10450,uu____10451);
              FStar_Syntax_Syntax.sigrng = uu____10452;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10454;
              FStar_Syntax_Syntax.sigattrs = uu____10455;_},uu____10456),uu____10457)
          ->
          FStar_Util.for_some
            (fun uu___116_10518  ->
               match uu___116_10518 with
               | FStar_Syntax_Syntax.RecordType uu____10519 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10528 -> true
               | uu____10537 -> false) quals
      | uu____10538 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10567 = lookup_qname env lid in
      match uu____10567 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____10588,uu____10589);
              FStar_Syntax_Syntax.sigrng = uu____10590;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10592;
              FStar_Syntax_Syntax.sigattrs = uu____10593;_},uu____10594),uu____10595)
          ->
          FStar_Util.for_some
            (fun uu___117_10652  ->
               match uu___117_10652 with
               | FStar_Syntax_Syntax.Action uu____10653 -> true
               | uu____10654 -> false) quals
      | uu____10655 -> false
let is_interpreted: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation] in
  fun env  ->
    fun head1  ->
      let uu____10687 =
        let uu____10688 = FStar_Syntax_Util.un_uinst head1 in
        uu____10688.FStar_Syntax_Syntax.n in
      match uu____10687 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10692 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____10759 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____10775) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____10792 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____10799 ->
                 FStar_Pervasives_Native.Some true
             | uu____10816 -> FStar_Pervasives_Native.Some false) in
      let uu____10817 =
        let uu____10820 = lookup_qname env lid in
        FStar_Util.bind_opt uu____10820 mapper in
      match uu____10817 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____10868 = lookup_qname env lid in
      match uu____10868 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10889,uu____10890,tps,uu____10892,uu____10893,uu____10894);
              FStar_Syntax_Syntax.sigrng = uu____10895;
              FStar_Syntax_Syntax.sigquals = uu____10896;
              FStar_Syntax_Syntax.sigmeta = uu____10897;
              FStar_Syntax_Syntax.sigattrs = uu____10898;_},uu____10899),uu____10900)
          -> FStar_List.length tps
      | uu____10963 ->
          let uu____10984 =
            let uu____10985 =
              let uu____10990 = name_not_found lid in
              (uu____10990, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____10985 in
          FStar_Exn.raise uu____10984
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____11032  ->
              match uu____11032 with
              | (d,uu____11040) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11053 = effect_decl_opt env l in
      match uu____11053 with
      | FStar_Pervasives_Native.None  ->
          let uu____11068 =
            let uu____11069 =
              let uu____11074 = name_not_found l in
              (uu____11074, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11069 in
          FStar_Exn.raise uu____11068
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  }
let join:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid))
          then
            (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____11140 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11193  ->
                       match uu____11193 with
                       | (m1,m2,uu____11206,uu____11207,uu____11208) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11140 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11225 =
                   let uu____11226 =
                     let uu____11231 =
                       let uu____11232 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11233 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11232
                         uu____11233 in
                     (uu____11231, (env.range)) in
                   FStar_Errors.Error uu____11226 in
                 FStar_Exn.raise uu____11225
             | FStar_Pervasives_Native.Some
                 (uu____11240,uu____11241,m3,j1,j2) -> (m3, j1, j2))
let monad_leq:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux:
  'Auu____11284 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11284)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11311 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11337  ->
                match uu____11337 with
                | (d,uu____11343) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11311 with
      | FStar_Pervasives_Native.None  ->
          let uu____11354 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11354
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11367 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11367 with
           | (uu____11378,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11388)::(wp,uu____11390)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11426 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m
let null_wp_for_eff:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          if
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Parser_Const.effect_GTot_lid
            then
              FStar_Syntax_Syntax.mk_GTotal' res_t
                (FStar_Pervasives_Native.Some res_u)
            else
              (let eff_name1 = norm_eff_name env eff_name in
               let ed = get_effect_decl env eff_name1 in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp in
               let null_wp_res =
                 let uu____11475 = get_range env in
                 let uu____11476 =
                   let uu____11479 =
                     let uu____11480 =
                       let uu____11495 =
                         let uu____11498 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11498] in
                       (null_wp, uu____11495) in
                     FStar_Syntax_Syntax.Tm_app uu____11480 in
                   FStar_Syntax_Syntax.mk uu____11479 in
                 uu____11476 FStar_Pervasives_Native.None uu____11475 in
               let uu____11504 =
                 let uu____11505 =
                   let uu____11514 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11514] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11505;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11504)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___129_11525 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___129_11525.order);
              joins = (uu___129_11525.joins)
            } in
          let uu___130_11534 = env in
          {
            solver = (uu___130_11534.solver);
            range = (uu___130_11534.range);
            curmodule = (uu___130_11534.curmodule);
            gamma = (uu___130_11534.gamma);
            gamma_cache = (uu___130_11534.gamma_cache);
            modules = (uu___130_11534.modules);
            expected_typ = (uu___130_11534.expected_typ);
            sigtab = (uu___130_11534.sigtab);
            is_pattern = (uu___130_11534.is_pattern);
            instantiate_imp = (uu___130_11534.instantiate_imp);
            effects;
            generalize = (uu___130_11534.generalize);
            letrecs = (uu___130_11534.letrecs);
            top_level = (uu___130_11534.top_level);
            check_uvars = (uu___130_11534.check_uvars);
            use_eq = (uu___130_11534.use_eq);
            is_iface = (uu___130_11534.is_iface);
            admit = (uu___130_11534.admit);
            lax = (uu___130_11534.lax);
            lax_universes = (uu___130_11534.lax_universes);
            failhard = (uu___130_11534.failhard);
            type_of = (uu___130_11534.type_of);
            universe_of = (uu___130_11534.universe_of);
            use_bv_sorts = (uu___130_11534.use_bv_sorts);
            qname_and_index = (uu___130_11534.qname_and_index);
            proof_ns = (uu___130_11534.proof_ns);
            synth = (uu___130_11534.synth);
            is_native_tactic = (uu___130_11534.is_native_tactic);
            identifier_info = (uu___130_11534.identifier_info);
            tc_hooks = (uu___130_11534.tc_hooks)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____11551 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____11551 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____11641 = (e1.mlift).mlift_wp t wp in
                              let uu____11642 = l1 t wp e in
                              l2 t uu____11641 uu____11642))
                | uu____11643 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____11682 = inst_tscheme lift_t in
            match uu____11682 with
            | (uu____11689,lift_t1) ->
                let uu____11691 =
                  let uu____11694 =
                    let uu____11695 =
                      let uu____11710 =
                        let uu____11713 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11714 =
                          let uu____11717 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____11717] in
                        uu____11713 :: uu____11714 in
                      (lift_t1, uu____11710) in
                    FStar_Syntax_Syntax.Tm_app uu____11695 in
                  FStar_Syntax_Syntax.mk uu____11694 in
                uu____11691 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____11758 = inst_tscheme lift_t in
            match uu____11758 with
            | (uu____11765,lift_t1) ->
                let uu____11767 =
                  let uu____11770 =
                    let uu____11771 =
                      let uu____11786 =
                        let uu____11789 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11790 =
                          let uu____11793 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____11794 =
                            let uu____11797 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11797] in
                          uu____11793 :: uu____11794 in
                        uu____11789 :: uu____11790 in
                      (lift_t1, uu____11786) in
                    FStar_Syntax_Syntax.Tm_app uu____11771 in
                  FStar_Syntax_Syntax.mk uu____11770 in
                uu____11767 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            } in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            } in
          let print_mlift l =
            let bogus_term s =
              let uu____11835 =
                let uu____11836 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____11836
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____11835 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____11840 =
              let uu____11841 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____11841 in
            let uu____11842 =
              let uu____11843 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____11861 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____11861) in
              FStar_Util.dflt "none" uu____11843 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11840
              uu____11842 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____11887  ->
                    match uu____11887 with
                    | (e,uu____11895) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____11914 =
            match uu____11914 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____11952 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        if FStar_Ident.lid_equals i k
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  if FStar_Ident.lid_equals j k
                                  then []
                                  else
                                    (let uu____11973 =
                                       let uu____11982 =
                                         find_edge order1 (i, k) in
                                       let uu____11985 =
                                         find_edge order1 (k, j) in
                                       (uu____11982, uu____11985) in
                                     match uu____11973 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12000 =
                                           compose_edges e1 e2 in
                                         [uu____12000]
                                     | uu____12001 -> []))))) in
              FStar_List.append order1 uu____11952 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____12030 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12032 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12032
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12030
                   then
                     let uu____12037 =
                       let uu____12038 =
                         let uu____12043 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12044 = get_range env in
                         (uu____12043, uu____12044) in
                       FStar_Errors.Error uu____12038 in
                     FStar_Exn.raise uu____12037
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                if FStar_Ident.lid_equals i j
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____12169 =
                                              let uu____12178 =
                                                find_edge order2 (i, k) in
                                              let uu____12181 =
                                                find_edge order2 (j, k) in
                                              (uu____12178, uu____12181) in
                                            match uu____12169 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12223,uu____12224)
                                                     ->
                                                     let uu____12231 =
                                                       let uu____12236 =
                                                         let uu____12237 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12237 in
                                                       let uu____12240 =
                                                         let uu____12241 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12241 in
                                                       (uu____12236,
                                                         uu____12240) in
                                                     (match uu____12231 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate";
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false ,false ) ->
                                                          bopt
                                                      | (true ,false ) ->
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____12276 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___131_12349 = env.effects in
              { decls = (uu___131_12349.decls); order = order2; joins } in
            let uu___132_12350 = env in
            {
              solver = (uu___132_12350.solver);
              range = (uu___132_12350.range);
              curmodule = (uu___132_12350.curmodule);
              gamma = (uu___132_12350.gamma);
              gamma_cache = (uu___132_12350.gamma_cache);
              modules = (uu___132_12350.modules);
              expected_typ = (uu___132_12350.expected_typ);
              sigtab = (uu___132_12350.sigtab);
              is_pattern = (uu___132_12350.is_pattern);
              instantiate_imp = (uu___132_12350.instantiate_imp);
              effects;
              generalize = (uu___132_12350.generalize);
              letrecs = (uu___132_12350.letrecs);
              top_level = (uu___132_12350.top_level);
              check_uvars = (uu___132_12350.check_uvars);
              use_eq = (uu___132_12350.use_eq);
              is_iface = (uu___132_12350.is_iface);
              admit = (uu___132_12350.admit);
              lax = (uu___132_12350.lax);
              lax_universes = (uu___132_12350.lax_universes);
              failhard = (uu___132_12350.failhard);
              type_of = (uu___132_12350.type_of);
              universe_of = (uu___132_12350.universe_of);
              use_bv_sorts = (uu___132_12350.use_bv_sorts);
              qname_and_index = (uu___132_12350.qname_and_index);
              proof_ns = (uu___132_12350.proof_ns);
              synth = (uu___132_12350.synth);
              is_native_tactic = (uu___132_12350.is_native_tactic);
              identifier_info = (uu___132_12350.identifier_info);
              tc_hooks = (uu___132_12350.tc_hooks)
            }))
      | uu____12351 -> env
let comp_to_comp_typ:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____12377 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12387 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12387 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12404 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12404 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12422 =
                     let uu____12423 =
                       let uu____12428 =
                         let uu____12429 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____12434 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____12441 =
                           let uu____12442 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____12442 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12429 uu____12434 uu____12441 in
                       (uu____12428, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12423 in
                   FStar_Exn.raise uu____12422)
                else ();
                (let inst1 =
                   let uu____12447 =
                     let uu____12456 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12456 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12473  ->
                        fun uu____12474  ->
                          match (uu____12473, uu____12474) with
                          | ((x,uu____12496),(t,uu____12498)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12447 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12517 =
                     let uu___133_12518 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___133_12518.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___133_12518.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___133_12518.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___133_12518.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12517
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux:
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let uu____12543 =
            let uu____12552 =
              norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
            effect_decl_opt env uu____12552 in
          match uu____12543 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12577 =
                only_reifiable &&
                  (let uu____12579 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____12579) in
              if uu____12577
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____12595 ->
                     let c1 = unfold_effect_abbrev env c in
                     let uu____12597 =
                       let uu____12610 =
                         FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
                       ((c1.FStar_Syntax_Syntax.result_typ), uu____12610) in
                     (match uu____12597 with
                      | (res_typ,wp) ->
                          let repr =
                            inst_effect_fun_with [u_c] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____12656 =
                            let uu____12659 = get_range env in
                            let uu____12660 =
                              let uu____12663 =
                                let uu____12664 =
                                  let uu____12679 =
                                    let uu____12682 =
                                      FStar_Syntax_Syntax.as_arg res_typ in
                                    [uu____12682; wp] in
                                  (repr, uu____12679) in
                                FStar_Syntax_Syntax.Tm_app uu____12664 in
                              FStar_Syntax_Syntax.mk uu____12663 in
                            uu____12660 FStar_Pervasives_Native.None
                              uu____12659 in
                          FStar_Pervasives_Native.Some uu____12656))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c
let reify_comp:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____12734 =
            let uu____12735 =
              let uu____12740 =
                let uu____12741 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____12741 in
              let uu____12742 = get_range env in (uu____12740, uu____12742) in
            FStar_Errors.Error uu____12735 in
          FStar_Exn.raise uu____12734 in
        let uu____12743 = effect_repr_aux true env c u_c in
        match uu____12743 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable: env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____12783 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____12792 =
        let uu____12793 = FStar_Syntax_Subst.compress t in
        uu____12793.FStar_Syntax_Syntax.n in
      match uu____12792 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____12796,c) ->
          is_reifiable_comp env c
      | uu____12814 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____12838)::uu____12839 -> x :: rest
        | (Binding_sig_inst uu____12848)::uu____12849 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12864 = push1 x rest1 in local :: uu____12864 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___134_12868 = env in
       let uu____12869 = push1 s env.gamma in
       {
         solver = (uu___134_12868.solver);
         range = (uu___134_12868.range);
         curmodule = (uu___134_12868.curmodule);
         gamma = uu____12869;
         gamma_cache = (uu___134_12868.gamma_cache);
         modules = (uu___134_12868.modules);
         expected_typ = (uu___134_12868.expected_typ);
         sigtab = (uu___134_12868.sigtab);
         is_pattern = (uu___134_12868.is_pattern);
         instantiate_imp = (uu___134_12868.instantiate_imp);
         effects = (uu___134_12868.effects);
         generalize = (uu___134_12868.generalize);
         letrecs = (uu___134_12868.letrecs);
         top_level = (uu___134_12868.top_level);
         check_uvars = (uu___134_12868.check_uvars);
         use_eq = (uu___134_12868.use_eq);
         is_iface = (uu___134_12868.is_iface);
         admit = (uu___134_12868.admit);
         lax = (uu___134_12868.lax);
         lax_universes = (uu___134_12868.lax_universes);
         failhard = (uu___134_12868.failhard);
         type_of = (uu___134_12868.type_of);
         universe_of = (uu___134_12868.universe_of);
         use_bv_sorts = (uu___134_12868.use_bv_sorts);
         qname_and_index = (uu___134_12868.qname_and_index);
         proof_ns = (uu___134_12868.proof_ns);
         synth = (uu___134_12868.synth);
         is_native_tactic = (uu___134_12868.is_native_tactic);
         identifier_info = (uu___134_12868.identifier_info);
         tc_hooks = (uu___134_12868.tc_hooks)
       })
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s)) in
      build_lattice env1 s
let push_sigelt_inst:
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us)) in
        build_lattice env1 s
let push_local_binding: env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___135_12906 = env in
      {
        solver = (uu___135_12906.solver);
        range = (uu___135_12906.range);
        curmodule = (uu___135_12906.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___135_12906.gamma_cache);
        modules = (uu___135_12906.modules);
        expected_typ = (uu___135_12906.expected_typ);
        sigtab = (uu___135_12906.sigtab);
        is_pattern = (uu___135_12906.is_pattern);
        instantiate_imp = (uu___135_12906.instantiate_imp);
        effects = (uu___135_12906.effects);
        generalize = (uu___135_12906.generalize);
        letrecs = (uu___135_12906.letrecs);
        top_level = (uu___135_12906.top_level);
        check_uvars = (uu___135_12906.check_uvars);
        use_eq = (uu___135_12906.use_eq);
        is_iface = (uu___135_12906.is_iface);
        admit = (uu___135_12906.admit);
        lax = (uu___135_12906.lax);
        lax_universes = (uu___135_12906.lax_universes);
        failhard = (uu___135_12906.failhard);
        type_of = (uu___135_12906.type_of);
        universe_of = (uu___135_12906.universe_of);
        use_bv_sorts = (uu___135_12906.use_bv_sorts);
        qname_and_index = (uu___135_12906.qname_and_index);
        proof_ns = (uu___135_12906.proof_ns);
        synth = (uu___135_12906.synth);
        is_native_tactic = (uu___135_12906.is_native_tactic);
        identifier_info = (uu___135_12906.identifier_info);
        tc_hooks = (uu___135_12906.tc_hooks)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv:
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___136_12940 = env in
             {
               solver = (uu___136_12940.solver);
               range = (uu___136_12940.range);
               curmodule = (uu___136_12940.curmodule);
               gamma = rest;
               gamma_cache = (uu___136_12940.gamma_cache);
               modules = (uu___136_12940.modules);
               expected_typ = (uu___136_12940.expected_typ);
               sigtab = (uu___136_12940.sigtab);
               is_pattern = (uu___136_12940.is_pattern);
               instantiate_imp = (uu___136_12940.instantiate_imp);
               effects = (uu___136_12940.effects);
               generalize = (uu___136_12940.generalize);
               letrecs = (uu___136_12940.letrecs);
               top_level = (uu___136_12940.top_level);
               check_uvars = (uu___136_12940.check_uvars);
               use_eq = (uu___136_12940.use_eq);
               is_iface = (uu___136_12940.is_iface);
               admit = (uu___136_12940.admit);
               lax = (uu___136_12940.lax);
               lax_universes = (uu___136_12940.lax_universes);
               failhard = (uu___136_12940.failhard);
               type_of = (uu___136_12940.type_of);
               universe_of = (uu___136_12940.universe_of);
               use_bv_sorts = (uu___136_12940.use_bv_sorts);
               qname_and_index = (uu___136_12940.qname_and_index);
               proof_ns = (uu___136_12940.proof_ns);
               synth = (uu___136_12940.synth);
               is_native_tactic = (uu___136_12940.is_native_tactic);
               identifier_info = (uu___136_12940.identifier_info);
               tc_hooks = (uu___136_12940.tc_hooks)
             }))
    | uu____12941 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____12965  ->
             match uu____12965 with | (x,uu____12971) -> push_bv env1 x) env
        bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___137_13001 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___137_13001.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___137_13001.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let push_let_binding:
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
let push_module: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___138_13036 = env in
       {
         solver = (uu___138_13036.solver);
         range = (uu___138_13036.range);
         curmodule = (uu___138_13036.curmodule);
         gamma = [];
         gamma_cache = (uu___138_13036.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___138_13036.sigtab);
         is_pattern = (uu___138_13036.is_pattern);
         instantiate_imp = (uu___138_13036.instantiate_imp);
         effects = (uu___138_13036.effects);
         generalize = (uu___138_13036.generalize);
         letrecs = (uu___138_13036.letrecs);
         top_level = (uu___138_13036.top_level);
         check_uvars = (uu___138_13036.check_uvars);
         use_eq = (uu___138_13036.use_eq);
         is_iface = (uu___138_13036.is_iface);
         admit = (uu___138_13036.admit);
         lax = (uu___138_13036.lax);
         lax_universes = (uu___138_13036.lax_universes);
         failhard = (uu___138_13036.failhard);
         type_of = (uu___138_13036.type_of);
         universe_of = (uu___138_13036.universe_of);
         use_bv_sorts = (uu___138_13036.use_bv_sorts);
         qname_and_index = (uu___138_13036.qname_and_index);
         proof_ns = (uu___138_13036.proof_ns);
         synth = (uu___138_13036.synth);
         is_native_tactic = (uu___138_13036.is_native_tactic);
         identifier_info = (uu___138_13036.identifier_info);
         tc_hooks = (uu___138_13036.tc_hooks)
       })
let push_univ_vars: env -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
let open_universes_in:
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____13073 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13073 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13101 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13101)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___139_13116 = env in
      {
        solver = (uu___139_13116.solver);
        range = (uu___139_13116.range);
        curmodule = (uu___139_13116.curmodule);
        gamma = (uu___139_13116.gamma);
        gamma_cache = (uu___139_13116.gamma_cache);
        modules = (uu___139_13116.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___139_13116.sigtab);
        is_pattern = (uu___139_13116.is_pattern);
        instantiate_imp = (uu___139_13116.instantiate_imp);
        effects = (uu___139_13116.effects);
        generalize = (uu___139_13116.generalize);
        letrecs = (uu___139_13116.letrecs);
        top_level = (uu___139_13116.top_level);
        check_uvars = (uu___139_13116.check_uvars);
        use_eq = false;
        is_iface = (uu___139_13116.is_iface);
        admit = (uu___139_13116.admit);
        lax = (uu___139_13116.lax);
        lax_universes = (uu___139_13116.lax_universes);
        failhard = (uu___139_13116.failhard);
        type_of = (uu___139_13116.type_of);
        universe_of = (uu___139_13116.universe_of);
        use_bv_sorts = (uu___139_13116.use_bv_sorts);
        qname_and_index = (uu___139_13116.qname_and_index);
        proof_ns = (uu___139_13116.proof_ns);
        synth = (uu___139_13116.synth);
        is_native_tactic = (uu___139_13116.is_native_tactic);
        identifier_info = (uu___139_13116.identifier_info);
        tc_hooks = (uu___139_13116.tc_hooks)
      }
let expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let clear_expected_typ:
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun env_  ->
    let uu____13142 = expected_typ env_ in
    ((let uu___140_13148 = env_ in
      {
        solver = (uu___140_13148.solver);
        range = (uu___140_13148.range);
        curmodule = (uu___140_13148.curmodule);
        gamma = (uu___140_13148.gamma);
        gamma_cache = (uu___140_13148.gamma_cache);
        modules = (uu___140_13148.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___140_13148.sigtab);
        is_pattern = (uu___140_13148.is_pattern);
        instantiate_imp = (uu___140_13148.instantiate_imp);
        effects = (uu___140_13148.effects);
        generalize = (uu___140_13148.generalize);
        letrecs = (uu___140_13148.letrecs);
        top_level = (uu___140_13148.top_level);
        check_uvars = (uu___140_13148.check_uvars);
        use_eq = false;
        is_iface = (uu___140_13148.is_iface);
        admit = (uu___140_13148.admit);
        lax = (uu___140_13148.lax);
        lax_universes = (uu___140_13148.lax_universes);
        failhard = (uu___140_13148.failhard);
        type_of = (uu___140_13148.type_of);
        universe_of = (uu___140_13148.universe_of);
        use_bv_sorts = (uu___140_13148.use_bv_sorts);
        qname_and_index = (uu___140_13148.qname_and_index);
        proof_ns = (uu___140_13148.proof_ns);
        synth = (uu___140_13148.synth);
        is_native_tactic = (uu___140_13148.is_native_tactic);
        identifier_info = (uu___140_13148.identifier_info);
        tc_hooks = (uu___140_13148.tc_hooks)
      }), uu____13142)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13163 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___118_13173  ->
                    match uu___118_13173 with
                    | Binding_sig (uu____13176,se) -> [se]
                    | uu____13182 -> [])) in
          FStar_All.pipe_right uu____13163 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___141_13189 = env in
       {
         solver = (uu___141_13189.solver);
         range = (uu___141_13189.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___141_13189.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___141_13189.expected_typ);
         sigtab = (uu___141_13189.sigtab);
         is_pattern = (uu___141_13189.is_pattern);
         instantiate_imp = (uu___141_13189.instantiate_imp);
         effects = (uu___141_13189.effects);
         generalize = (uu___141_13189.generalize);
         letrecs = (uu___141_13189.letrecs);
         top_level = (uu___141_13189.top_level);
         check_uvars = (uu___141_13189.check_uvars);
         use_eq = (uu___141_13189.use_eq);
         is_iface = (uu___141_13189.is_iface);
         admit = (uu___141_13189.admit);
         lax = (uu___141_13189.lax);
         lax_universes = (uu___141_13189.lax_universes);
         failhard = (uu___141_13189.failhard);
         type_of = (uu___141_13189.type_of);
         universe_of = (uu___141_13189.universe_of);
         use_bv_sorts = (uu___141_13189.use_bv_sorts);
         qname_and_index = (uu___141_13189.qname_and_index);
         proof_ns = (uu___141_13189.proof_ns);
         synth = (uu___141_13189.synth);
         is_native_tactic = (uu___141_13189.is_native_tactic);
         identifier_info = (uu___141_13189.identifier_info);
         tc_hooks = (uu___141_13189.tc_hooks)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13271)::tl1 -> aux out tl1
      | (Binding_lid (uu____13275,(uu____13276,t)))::tl1 ->
          let uu____13291 =
            let uu____13298 = FStar_Syntax_Free.uvars t in
            ext out uu____13298 in
          aux uu____13291 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13305;
            FStar_Syntax_Syntax.index = uu____13306;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13313 =
            let uu____13320 = FStar_Syntax_Free.uvars t in
            ext out uu____13320 in
          aux uu____13313 tl1
      | (Binding_sig uu____13327)::uu____13328 -> out
      | (Binding_sig_inst uu____13337)::uu____13338 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13394)::tl1 -> aux out tl1
      | (Binding_univ uu____13406)::tl1 -> aux out tl1
      | (Binding_lid (uu____13410,(uu____13411,t)))::tl1 ->
          let uu____13426 =
            let uu____13429 = FStar_Syntax_Free.univs t in
            ext out uu____13429 in
          aux uu____13426 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13432;
            FStar_Syntax_Syntax.index = uu____13433;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13440 =
            let uu____13443 = FStar_Syntax_Free.univs t in
            ext out uu____13443 in
          aux uu____13440 tl1
      | (Binding_sig uu____13446)::uu____13447 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13501)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13517 = FStar_Util.fifo_set_add uname out in
          aux uu____13517 tl1
      | (Binding_lid (uu____13520,(uu____13521,t)))::tl1 ->
          let uu____13536 =
            let uu____13539 = FStar_Syntax_Free.univnames t in
            ext out uu____13539 in
          aux uu____13536 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13542;
            FStar_Syntax_Syntax.index = uu____13543;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13550 =
            let uu____13553 = FStar_Syntax_Free.univnames t in
            ext out uu____13553 in
          aux uu____13550 tl1
      | (Binding_sig uu____13556)::uu____13557 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___119_13582  ->
            match uu___119_13582 with
            | Binding_var x -> [x]
            | Binding_lid uu____13586 -> []
            | Binding_sig uu____13591 -> []
            | Binding_univ uu____13598 -> []
            | Binding_sig_inst uu____13599 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____13616 =
      let uu____13619 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____13619
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____13616 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____13644 =
      let uu____13645 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___120_13655  ->
                match uu___120_13655 with
                | Binding_var x ->
                    let uu____13657 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____13657
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13660) ->
                    let uu____13661 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____13661
                | Binding_sig (ls,uu____13663) ->
                    let uu____13668 =
                      let uu____13669 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13669
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____13668
                | Binding_sig_inst (ls,uu____13679,uu____13680) ->
                    let uu____13685 =
                      let uu____13686 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13686
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____13685)) in
      FStar_All.pipe_right uu____13645 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____13644 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____13705 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____13705
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____13733  ->
                 fun uu____13734  ->
                   match (uu____13733, uu____13734) with
                   | ((b1,uu____13752),(b2,uu____13754)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___121_13816  ->
             match uu___121_13816 with
             | Binding_sig (lids,uu____13822) -> FStar_List.append lids keys
             | uu____13827 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13833  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13869) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13888,uu____13889) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____13926 = list_prefix p path1 in
            if uu____13926 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13940 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____13940
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___142_13970 = e in
            {
              solver = (uu___142_13970.solver);
              range = (uu___142_13970.range);
              curmodule = (uu___142_13970.curmodule);
              gamma = (uu___142_13970.gamma);
              gamma_cache = (uu___142_13970.gamma_cache);
              modules = (uu___142_13970.modules);
              expected_typ = (uu___142_13970.expected_typ);
              sigtab = (uu___142_13970.sigtab);
              is_pattern = (uu___142_13970.is_pattern);
              instantiate_imp = (uu___142_13970.instantiate_imp);
              effects = (uu___142_13970.effects);
              generalize = (uu___142_13970.generalize);
              letrecs = (uu___142_13970.letrecs);
              top_level = (uu___142_13970.top_level);
              check_uvars = (uu___142_13970.check_uvars);
              use_eq = (uu___142_13970.use_eq);
              is_iface = (uu___142_13970.is_iface);
              admit = (uu___142_13970.admit);
              lax = (uu___142_13970.lax);
              lax_universes = (uu___142_13970.lax_universes);
              failhard = (uu___142_13970.failhard);
              type_of = (uu___142_13970.type_of);
              universe_of = (uu___142_13970.universe_of);
              use_bv_sorts = (uu___142_13970.use_bv_sorts);
              qname_and_index = (uu___142_13970.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___142_13970.synth);
              is_native_tactic = (uu___142_13970.is_native_tactic);
              identifier_info = (uu___142_13970.identifier_info);
              tc_hooks = (uu___142_13970.tc_hooks)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___143_13997 = e in
    {
      solver = (uu___143_13997.solver);
      range = (uu___143_13997.range);
      curmodule = (uu___143_13997.curmodule);
      gamma = (uu___143_13997.gamma);
      gamma_cache = (uu___143_13997.gamma_cache);
      modules = (uu___143_13997.modules);
      expected_typ = (uu___143_13997.expected_typ);
      sigtab = (uu___143_13997.sigtab);
      is_pattern = (uu___143_13997.is_pattern);
      instantiate_imp = (uu___143_13997.instantiate_imp);
      effects = (uu___143_13997.effects);
      generalize = (uu___143_13997.generalize);
      letrecs = (uu___143_13997.letrecs);
      top_level = (uu___143_13997.top_level);
      check_uvars = (uu___143_13997.check_uvars);
      use_eq = (uu___143_13997.use_eq);
      is_iface = (uu___143_13997.is_iface);
      admit = (uu___143_13997.admit);
      lax = (uu___143_13997.lax);
      lax_universes = (uu___143_13997.lax_universes);
      failhard = (uu___143_13997.failhard);
      type_of = (uu___143_13997.type_of);
      universe_of = (uu___143_13997.universe_of);
      use_bv_sorts = (uu___143_13997.use_bv_sorts);
      qname_and_index = (uu___143_13997.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___143_13997.synth);
      is_native_tactic = (uu___143_13997.is_native_tactic);
      identifier_info = (uu___143_13997.identifier_info);
      tc_hooks = (uu___143_13997.tc_hooks)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____14012::rest ->
        let uu___144_14016 = e in
        {
          solver = (uu___144_14016.solver);
          range = (uu___144_14016.range);
          curmodule = (uu___144_14016.curmodule);
          gamma = (uu___144_14016.gamma);
          gamma_cache = (uu___144_14016.gamma_cache);
          modules = (uu___144_14016.modules);
          expected_typ = (uu___144_14016.expected_typ);
          sigtab = (uu___144_14016.sigtab);
          is_pattern = (uu___144_14016.is_pattern);
          instantiate_imp = (uu___144_14016.instantiate_imp);
          effects = (uu___144_14016.effects);
          generalize = (uu___144_14016.generalize);
          letrecs = (uu___144_14016.letrecs);
          top_level = (uu___144_14016.top_level);
          check_uvars = (uu___144_14016.check_uvars);
          use_eq = (uu___144_14016.use_eq);
          is_iface = (uu___144_14016.is_iface);
          admit = (uu___144_14016.admit);
          lax = (uu___144_14016.lax);
          lax_universes = (uu___144_14016.lax_universes);
          failhard = (uu___144_14016.failhard);
          type_of = (uu___144_14016.type_of);
          universe_of = (uu___144_14016.universe_of);
          use_bv_sorts = (uu___144_14016.use_bv_sorts);
          qname_and_index = (uu___144_14016.qname_and_index);
          proof_ns = rest;
          synth = (uu___144_14016.synth);
          is_native_tactic = (uu___144_14016.is_native_tactic);
          identifier_info = (uu___144_14016.identifier_info);
          tc_hooks = (uu___144_14016.tc_hooks)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___145_14029 = e in
      {
        solver = (uu___145_14029.solver);
        range = (uu___145_14029.range);
        curmodule = (uu___145_14029.curmodule);
        gamma = (uu___145_14029.gamma);
        gamma_cache = (uu___145_14029.gamma_cache);
        modules = (uu___145_14029.modules);
        expected_typ = (uu___145_14029.expected_typ);
        sigtab = (uu___145_14029.sigtab);
        is_pattern = (uu___145_14029.is_pattern);
        instantiate_imp = (uu___145_14029.instantiate_imp);
        effects = (uu___145_14029.effects);
        generalize = (uu___145_14029.generalize);
        letrecs = (uu___145_14029.letrecs);
        top_level = (uu___145_14029.top_level);
        check_uvars = (uu___145_14029.check_uvars);
        use_eq = (uu___145_14029.use_eq);
        is_iface = (uu___145_14029.is_iface);
        admit = (uu___145_14029.admit);
        lax = (uu___145_14029.lax);
        lax_universes = (uu___145_14029.lax_universes);
        failhard = (uu___145_14029.failhard);
        type_of = (uu___145_14029.type_of);
        universe_of = (uu___145_14029.universe_of);
        use_bv_sorts = (uu___145_14029.use_bv_sorts);
        qname_and_index = (uu___145_14029.qname_and_index);
        proof_ns = ns;
        synth = (uu___145_14029.synth);
        is_native_tactic = (uu___145_14029.is_native_tactic);
        identifier_info = (uu___145_14029.identifier_info);
        tc_hooks = (uu___145_14029.tc_hooks)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14058 =
        FStar_List.map
          (fun fpns  ->
             let uu____14080 =
               let uu____14081 =
                 let uu____14082 =
                   FStar_List.map
                     (fun uu____14094  ->
                        match uu____14094 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____14082 in
               Prims.strcat uu____14081 "]" in
             Prims.strcat "[" uu____14080) pns in
      FStar_String.concat ";" uu____14058 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____14110  -> ());
    push = (fun uu____14112  -> ());
    pop = (fun uu____14114  -> ());
    mark = (fun uu____14116  -> ());
    reset_mark = (fun uu____14118  -> ());
    commit_mark = (fun uu____14120  -> ());
    encode_modul = (fun uu____14123  -> fun uu____14124  -> ());
    encode_sig = (fun uu____14127  -> fun uu____14128  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14134 =
             let uu____14141 = FStar_Options.peek () in (e, g, uu____14141) in
           [uu____14134]);
    solve = (fun uu____14157  -> fun uu____14158  -> fun uu____14159  -> ());
    is_trivial = (fun uu____14166  -> fun uu____14167  -> false);
    finish = (fun uu____14169  -> ());
    refresh = (fun uu____14171  -> ())
  }