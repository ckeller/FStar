
open Prims

type effect_cost =
| ForFree
| NotForFree


let is_ForFree = (fun _discr_ -> (match (_discr_) with
| ForFree (_) -> begin
true
end
| _ -> begin
false
end))


let is_NotForFree = (fun _discr_ -> (match (_discr_) with
| NotForFree (_) -> begin
true
end
| _ -> begin
false
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _146_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _146_5))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_17 = env
in {FStar_TypeChecker_Env.solver = _57_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_17.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_20 = env
in {FStar_TypeChecker_Env.solver = _57_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_20.FStar_TypeChecker_Env.use_bv_sorts}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _146_19 = (let _146_18 = (FStar_Syntax_Syntax.as_arg v)
in (let _146_17 = (let _146_16 = (FStar_Syntax_Syntax.as_arg tl)
in (_146_16)::[])
in (_146_18)::_146_17))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _146_19 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _57_30 -> begin
false
end))


let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _146_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _146_32 env t)))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _146_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _146_37 env c)))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_47 -> begin
(

let fvs' = (let _146_50 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _146_50))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _57_54 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _146_54 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _146_54))
end
| Some (head) -> begin
(let _146_56 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_55 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _146_56 _146_55)))
end)
in (let _146_59 = (let _146_58 = (let _146_57 = (FStar_TypeChecker_Env.get_range env)
in (msg, _146_57))
in FStar_Syntax_Syntax.Error (_146_58))
in (Prims.raise _146_59)))
end))
in (

let s = (let _146_61 = (let _146_60 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_60))
in (FStar_TypeChecker_Util.new_uvar env _146_61))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _57_63 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(

let _57_66 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_67 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _146_66 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_67 _146_66)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)


let maybe_make_subst = (fun _57_2 -> (match (_57_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _57_75 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _57_81 = lc
in {FStar_Syntax_Syntax.eff_name = _57_81.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_81.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_83 -> (match (()) with
| () -> begin
(let _146_80 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _146_80 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _146_89 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _146_89))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(

let _57_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_91 = (FStar_Syntax_Print.term_to_string t)
in (let _146_90 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _146_91 _146_90)))
end else begin
()
end
in (

let _57_101 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_101) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_105 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_105) with
| (e, g) -> begin
(

let _57_106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_93 = (FStar_Syntax_Print.term_to_string t)
in (let _146_92 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _146_93 _146_92)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _57_111 = (let _146_99 = (FStar_All.pipe_left (fun _146_98 -> Some (_146_98)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _146_99 env e lc g))
in (match (_57_111) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_57_115) with
| (e, lc, g) -> begin
(

let _57_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _146_100))
end else begin
()
end
in (e, lc, g))
end)))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(

let _57_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_131 -> (match (_57_131) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_57_133) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _146_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_146_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _146_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_146_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _146_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_146_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _146_116 = (norm_c env c)
in (e, _146_116, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(

let _57_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_119 = (FStar_Syntax_Print.term_to_string e)
in (let _146_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_119 _146_118 _146_117))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_122 = (FStar_Syntax_Print.term_to_string e)
in (let _146_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_122 _146_121 _146_120))))
end else begin
()
end
in (

let _57_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_149) with
| (e, _57_147, g) -> begin
(

let g = (let _146_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _146_123 "could not prove post-condition" g))
in (

let _57_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _146_125 _146_124)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))


let no_logical_guard = (fun env _57_157 -> (match (_57_157) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _146_131 = (let _146_130 = (let _146_129 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _146_128 = (FStar_TypeChecker_Env.get_range env)
in (_146_129, _146_128)))
in FStar_Syntax_Syntax.Error (_146_130))
in (Prims.raise _146_131))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _146_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _146_134))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_181; FStar_Syntax_Syntax.result_typ = _57_179; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _57_173))::[]; FStar_Syntax_Syntax.flags = _57_170}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_188 -> (match (_57_188) with
| (b, _57_187) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_192) -> begin
(let _146_141 = (let _146_140 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _146_140))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _146_141))
end))
end
| _57_196 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env = (

let _57_203 = env
in {FStar_TypeChecker_Env.solver = _57_203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_203.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_215 -> (match (_57_215) with
| (b, _57_214) -> begin
(

let t = (let _146_155 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _146_155))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_224 -> begin
(let _146_156 = (FStar_Syntax_Syntax.bv_to_name b)
in (_146_156)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _57_230 = (FStar_Syntax_Util.head_and_args dec)
in (match (_57_230) with
| (head, _57_229) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _57_234 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.DECREASES (_57_238) -> begin
true
end
| _57_241 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _57_246 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _57_251 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _57_256 -> (match (_57_256) with
| (l, t) -> begin
(match ((let _146_162 = (FStar_Syntax_Subst.compress t)
in _146_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_263 -> (match (_57_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _146_166 = (let _146_165 = (let _146_164 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_146_164))
in (FStar_Syntax_Syntax.new_bv _146_165 x.FStar_Syntax_Syntax.sort))
in (_146_166, imp))
end else begin
(x, imp)
end
end))))
in (

let _57_267 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_267) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _146_170 = (let _146_169 = (FStar_Syntax_Syntax.as_arg dec)
in (let _146_168 = (let _146_167 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_146_167)::[])
in (_146_169)::_146_168))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _146_170 None r))
in (

let _57_274 = (FStar_Util.prefix formals)
in (match (_57_274) with
| (bs, (last, imp)) -> begin
(

let last = (

let _57_275 = last
in (let _146_171 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_171}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _57_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_174 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_173 = (FStar_Syntax_Print.term_to_string t)
in (let _146_172 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _146_174 _146_173 _146_172))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _57_283 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _57_286 = env
in {FStar_TypeChecker_Env.solver = _57_286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_286.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _57_291 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_242 = (let _146_240 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _146_240))
in (let _146_241 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _146_242 _146_241)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_295) -> begin
(let _146_246 = (FStar_Syntax_Subst.compress e)
in (tc_term env _146_246))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _57_336 = (tc_tot_or_gtot_term env e)
in (match (_57_336) with
| (e, c, g) -> begin
(

let g = (

let _57_337 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_337.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _57_347 = (FStar_Syntax_Util.type_u ())
in (match (_57_347) with
| (t, u) -> begin
(

let _57_351 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_351) with
| (e, c, g) -> begin
(

let _57_358 = (

let _57_355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_355) with
| (env, _57_354) -> begin
(tc_pats env pats)
end))
in (match (_57_358) with
| (pats, g') -> begin
(

let g' = (

let _57_359 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_359.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_359.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_359.FStar_TypeChecker_Env.implicits})
in (let _146_248 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_247 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_146_248, c, _146_247))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _146_249 = (FStar_Syntax_Subst.compress e)
in _146_249.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_368, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_375; FStar_Syntax_Syntax.lbtyp = _57_373; FStar_Syntax_Syntax.lbeff = _57_371; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _57_386 = (let _146_250 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _146_250 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(

let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (

let e = (let _146_255 = (let _146_254 = (let _146_253 = (let _146_252 = (let _146_251 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_146_251)::[])
in (false, _146_252))
in (_146_253, e2))
in FStar_Syntax_Syntax.Tm_let (_146_254))
in (FStar_Syntax_Syntax.mk _146_255 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_256 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _146_256)))))
end))
end))
end
| _57_395 -> begin
(

let _57_399 = (tc_term env e)
in (match (_57_399) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _57_408 = (tc_term env e)
in (match (_57_408) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_414) -> begin
(

let _57_421 = (tc_comp env expected_c)
in (match (_57_421) with
| (expected_c, _57_419, g) -> begin
(

let _57_425 = (tc_term env e)
in (match (_57_425) with
| (e, c', g') -> begin
(

let _57_429 = (let _146_258 = (let _146_257 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _146_257))
in (check_expected_effect env (Some (expected_c)) _146_258))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _146_261 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_260 = (let _146_259 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _146_259))
in (_146_261, (FStar_Syntax_Util.lcomp_of_comp expected_c), _146_260))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_435) -> begin
(

let _57_440 = (FStar_Syntax_Util.type_u ())
in (match (_57_440) with
| (k, u) -> begin
(

let _57_445 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_445) with
| (t, _57_443, f) -> begin
(

let _57_449 = (let _146_262 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _146_262 e))
in (match (_57_449) with
| (e, c, g) -> begin
(

let _57_453 = (let _146_266 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_266 e c f))
in (match (_57_453) with
| (c, f) -> begin
(

let _57_457 = (let _146_267 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _146_267 c))
in (match (_57_457) with
| (e, c, f2) -> begin
(let _146_269 = (let _146_268 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _146_268))
in (e, c, _146_269))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _146_271 = (let _146_270 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_270 Prims.fst))
in (FStar_All.pipe_right _146_271 instantiate_both))
in (

let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_273 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_272 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _146_273 _146_272)))
end else begin
()
end
in (

let _57_469 = (tc_term (no_inst env) head)
in (match (_57_469) with
| (head, chead, g_head) -> begin
(

let _57_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _146_274 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _146_274))
end else begin
(let _146_275 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _146_275))
end
in (match (_57_473) with
| (e, c, g) -> begin
(

let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_276 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _146_276))
end else begin
()
end
in (

let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (

let _57_480 = (comp_check_expected_typ env0 e c)
in (match (_57_480) with
| (e, c, g') -> begin
(

let gimp = (match ((let _146_277 = (FStar_Syntax_Subst.compress head)
in _146_277.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_483) -> begin
(

let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (

let _57_487 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_487.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_487.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_487.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_490 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _146_278 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _146_278))
in (

let _57_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_279 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _146_279))
end else begin
()
end
in (e, c, gres))))
end))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let _57_501 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_501) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _57_506 = (tc_term env1 e1)
in (match (_57_506) with
| (e1, c1, g1) -> begin
(

let _57_517 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(

let _57_513 = (FStar_Syntax_Util.type_u ())
in (match (_57_513) with
| (k, _57_512) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _146_280 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_146_280, res_t)))
end))
end)
in (match (_57_517) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _57_534 = (

let _57_531 = (FStar_List.fold_right (fun _57_525 _57_528 -> (match ((_57_525, _57_528)) with
| ((_57_521, f, c, g), (caccum, gaccum)) -> begin
(let _146_283 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _146_283))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_531) with
| (cases, g) -> begin
(let _146_284 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_146_284, g))
end))
in (match (_57_534) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _146_288 = (let _146_287 = (let _146_286 = (FStar_List.map (fun _57_543 -> (match (_57_543) with
| (f, _57_538, _57_540, _57_542) -> begin
f
end)) t_eqns)
in (e1, _146_286))
in FStar_Syntax_Syntax.Tm_match (_146_287))
in (FStar_Syntax_Syntax.mk _146_288 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_546 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_291 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_290 = (let _146_289 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_289))
in (FStar_Util.print2 "(%s) comp type = %s\n" _146_291 _146_290)))
end else begin
()
end
in (let _146_292 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _146_292))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_558); FStar_Syntax_Syntax.lbunivs = _57_556; FStar_Syntax_Syntax.lbtyp = _57_554; FStar_Syntax_Syntax.lbeff = _57_552; FStar_Syntax_Syntax.lbdef = _57_550})::[]), _57_564) -> begin
(

let _57_567 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_293 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_293))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_571), _57_574) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_589); FStar_Syntax_Syntax.lbunivs = _57_587; FStar_Syntax_Syntax.lbtyp = _57_585; FStar_Syntax_Syntax.lbeff = _57_583; FStar_Syntax_Syntax.lbdef = _57_581})::_57_579), _57_595) -> begin
(

let _57_598 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_294 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_294))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_602), _57_605) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _57_619 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_619) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_308 = (let _146_307 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_307))
in FStar_Util.Inr (_146_308))
end
in (

let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_629 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _146_314 = (let _146_313 = (let _146_312 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _146_311 = (FStar_TypeChecker_Env.get_range env)
in (_146_312, _146_311)))
in FStar_Syntax_Syntax.Error (_146_313))
in (Prims.raise _146_314))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _146_315 = (FStar_Syntax_Subst.compress t1)
in _146_315.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_640) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_643 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _57_645 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_645.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_645.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_645.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_651 = (FStar_Syntax_Util.type_u ())
in (match (_57_651) with
| (k, u) -> begin
(

let t = (FStar_TypeChecker_Util.new_uvar env k)
in (

let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let _57_657 = x
in {FStar_Syntax_Syntax.ppname = _57_657.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_657.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_663 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_663) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_317 = (let _146_316 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_316))
in FStar_Util.Inr (_146_317))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_670; FStar_Syntax_Syntax.pos = _57_668; FStar_Syntax_Syntax.vars = _57_666}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_680 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_680) with
| (us', t) -> begin
(

let _57_687 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_320 = (let _146_319 = (let _146_318 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_318))
in FStar_Syntax_Syntax.Error (_146_319))
in (Prims.raise _146_320))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_686 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_689 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_691 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_691.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_691.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_689.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_689.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _146_323 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_323 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_699 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_699) with
| (us, t) -> begin
(

let fv' = (

let _57_700 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_702 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_702.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_702.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_700.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_700.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _146_324 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_324 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_716 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_716) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_721 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_721) with
| (env, _57_720) -> begin
(

let _57_726 = (tc_binders env bs)
in (match (_57_726) with
| (bs, env, g, us) -> begin
(

let _57_730 = (tc_comp env c)
in (match (_57_730) with
| (c, uc, f) -> begin
(

let e = (

let _57_731 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_731.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_731.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_731.FStar_Syntax_Syntax.vars})
in (

let _57_734 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _146_325 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _146_325))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (tc_universe env u)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _57_750 = (let _146_327 = (let _146_326 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_326)::[])
in (FStar_Syntax_Subst.open_term _146_327 phi))
in (match (_57_750) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_755 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_755) with
| (env, _57_754) -> begin
(

let _57_760 = (let _146_328 = (FStar_List.hd x)
in (tc_binder env _146_328))
in (match (_57_760) with
| (x, env, f1, u) -> begin
(

let _57_761 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_331 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_330 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_329 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_331 _146_330 _146_329))))
end else begin
()
end
in (

let _57_766 = (FStar_Syntax_Util.type_u ())
in (match (_57_766) with
| (t_phi, _57_765) -> begin
(

let _57_771 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_771) with
| (phi, _57_769, f2) -> begin
(

let e = (

let _57_772 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_772.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_772.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_772.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _146_332 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_332))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_780) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_786 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_333 = (FStar_Syntax_Print.term_to_string (

let _57_784 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_784.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_784.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_784.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_333))
end else begin
()
end
in (

let _57_790 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_790) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_792 -> begin
(let _146_335 = (let _146_334 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_334))
in (FStar_All.failwith _146_335))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_797) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_800, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_805, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_813, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_821, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_829, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_837, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_845, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_853, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_861, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_869) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_872) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_875) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_879) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_882 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_889 = (FStar_Syntax_Util.type_u ())
in (match (_57_889) with
| (k, u) -> begin
(

let _57_894 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_894) with
| (t, _57_892, g) -> begin
(let _146_340 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_340, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_899 = (FStar_Syntax_Util.type_u ())
in (match (_57_899) with
| (k, u) -> begin
(

let _57_904 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_904) with
| (t, _57_902, g) -> begin
(let _146_341 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_341, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _146_343 = (let _146_342 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_342)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_343 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_913 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_913) with
| (tc, _57_911, f) -> begin
(

let _57_917 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_917) with
| (_57_915, args) -> begin
(

let _57_920 = (let _146_345 = (FStar_List.hd args)
in (let _146_344 = (FStar_List.tl args)
in (_146_345, _146_344)))
in (match (_57_920) with
| (res, args) -> begin
(

let _57_936 = (let _146_347 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_927 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_927) with
| (env, _57_926) -> begin
(

let _57_932 = (tc_tot_or_gtot_term env e)
in (match (_57_932) with
| (e, _57_930, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_347 FStar_List.unzip))
in (match (_57_936) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_941 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_349 = (FStar_Syntax_Syntax.mk_Comp (

let _57_943 = c
in {FStar_Syntax_Syntax.effect_name = _57_943.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_943.FStar_Syntax_Syntax.flags}))
in (let _146_348 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_349, u, _146_348))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_951) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_354 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_354))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_355 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_355))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_359 = (let _146_358 = (let _146_357 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_356 = (FStar_TypeChecker_Env.get_range env)
in (_146_357, _146_356)))
in FStar_Syntax_Syntax.Error (_146_358))
in (Prims.raise _146_359))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_360 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_360 Prims.snd))
end
| _57_966 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _146_369 = (let _146_368 = (let _146_367 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_367, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_368))
in (Prims.raise _146_369)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_984 bs bs_expected -> (match (_57_984) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_1015 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_386 = (let _146_385 = (let _146_384 = (let _146_382 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_382))
in (let _146_383 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_384, _146_383)))
in FStar_Syntax_Syntax.Error (_146_385))
in (Prims.raise _146_386))
end
| _57_1014 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_1032 = (match ((let _146_387 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_387.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1020 -> begin
(

let _57_1021 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_388 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_388))
end else begin
()
end
in (

let _57_1027 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1027) with
| (t, _57_1025, g1) -> begin
(

let g2 = (let _146_390 = (FStar_TypeChecker_Env.get_range env)
in (let _146_389 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_390 "Type annotation on parameter incompatible with the expected type" _146_389)))
in (

let g = (let _146_391 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_391))
in (t, g)))
end)))
end)
in (match (_57_1032) with
| (t, g) -> begin
(

let hd = (

let _57_1033 = hd
in {FStar_Syntax_Syntax.ppname = _57_1033.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1033.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (maybe_push_binding env b)
in (

let subst = (let _146_392 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _146_392))
in (aux (env, (b)::out, g, subst) bs bs_expected))))))
end))))
end
| (rest, []) -> begin
(env, (FStar_List.rev out), Some (FStar_Util.Inl (rest)), g, subst)
end
| ([], rest) -> begin
(env, (FStar_List.rev out), Some (FStar_Util.Inr (rest)), g, subst)
end)
end))
in (aux (env, [], FStar_TypeChecker_Rel.trivial_guard, []) bs bs_expected)))
in (

let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(

let _57_1054 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1053 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1061 = (tc_binders env bs)
in (match (_57_1061) with
| (bs, envbody, g, _57_1060) -> begin
(

let _57_1079 = (match ((let _146_399 = (FStar_Syntax_Subst.compress body)
in _146_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1066) -> begin
(

let _57_1073 = (tc_comp envbody c)
in (match (_57_1073) with
| (c, _57_1071, g') -> begin
(let _146_400 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_400))
end))
end
| _57_1075 -> begin
(None, body, g)
end)
in (match (_57_1079) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _146_405 = (FStar_Syntax_Subst.compress t)
in _146_405.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1106 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1105 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1113 = (tc_binders env bs)
in (match (_57_1113) with
| (bs, envbody, g, _57_1112) -> begin
(

let _57_1117 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1117) with
| (envbody, _57_1116) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1120) -> begin
(

let _57_1131 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1131) with
| (_57_1124, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1138 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1138) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1149 c_expected -> (match (_57_1149) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _146_416 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _146_416))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _146_417 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_417))
in (let _146_418 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _146_418)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1170 = (check_binders env more_bs bs_expected)
in (match (_57_1170) with
| (env, bs', more, guard', subst) -> begin
(let _146_420 = (let _146_419 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_419, subst))
in (handle_more _146_420 c_expected))
end))
end
| _57_1172 -> begin
(let _146_422 = (let _146_421 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_421))
in (fail _146_422 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_423 = (check_binders env bs bs_expected)
in (handle_more _146_423 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1178 = envbody
in {FStar_TypeChecker_Env.solver = _57_1178.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1178.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1178.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1178.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1178.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1178.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1178.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1178.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1178.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1178.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1178.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1178.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1178.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1178.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1178.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1178.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1178.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1178.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1178.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1178.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1183 _57_1186 -> (match ((_57_1183, _57_1186)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1192 = (let _146_433 = (let _146_432 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_432 Prims.fst))
in (tc_term _146_433 t))
in (match (_57_1192) with
| (t, _57_1189, _57_1191) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_434 = (FStar_Syntax_Syntax.mk_binder (

let _57_1196 = x
in {FStar_Syntax_Syntax.ppname = _57_1196.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1196.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_434)::letrec_binders)
end
| _57_1199 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1205 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1205) with
| (envbody, bs, g, c) -> begin
(

let _57_1208 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1208) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1211 -> begin
if (not (norm)) then begin
(let _146_435 = (unfold_whnf env t)
in (as_function_typ true _146_435))
end else begin
(

let _57_1221 = (expected_function_typ env None body)
in (match (_57_1221) with
| (_57_1213, bs, _57_1216, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1225 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1225) with
| (env, topt) -> begin
(

let _57_1229 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_436 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_436 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1238 = (expected_function_typ env topt body)
in (match (_57_1238) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1244 = (tc_term (

let _57_1239 = envbody
in {FStar_TypeChecker_Env.solver = _57_1239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1239.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1239.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1239.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1244) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1246 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_439 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_438 = (let _146_437 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_437))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_439 _146_438)))
end else begin
()
end
in (

let _57_1253 = (let _146_441 = (let _146_440 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_440))
in (check_expected_effect (

let _57_1248 = envbody
in {FStar_TypeChecker_Env.solver = _57_1248.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1248.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1248.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1248.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1248.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1248.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1248.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1248.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1248.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1248.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1248.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1248.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1248.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1248.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1248.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1248.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1248.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1248.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1248.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1248.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_441))
in (match (_57_1253) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_442 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_442))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _146_445 = (let _146_444 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_443 -> FStar_Util.Inl (_146_443)))
in Some (_146_444))
in (FStar_Syntax_Util.abs bs body _146_445))
in (

let _57_1276 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1265) -> begin
(e, t, guard)
end
| _57_1268 -> begin
(

let _57_1271 = if use_teq then begin
(let _146_446 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_446))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1271) with
| (e, guard') -> begin
(let _146_447 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_447))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1276) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1280 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1280) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in (

let _57_1290 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_456 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_455 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_456 _146_455)))
end else begin
()
end
in (

let rec check_function_app = (fun norm tf -> (match ((let _146_461 = (FStar_Syntax_Util.unrefine tf)
in _146_461.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| ((e, imp))::tl -> begin
(

let _57_1324 = (tc_term env e)
in (match (_57_1324) with
| (e, c, g_e) -> begin
(

let _57_1328 = (tc_args env tl)
in (match (_57_1328) with
| (args, comps, g_rest) -> begin
(let _146_466 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _146_466))
end))
end))
end))
in (

let _57_1332 = (tc_args env args)
in (match (_57_1332) with
| (args, comps, g_args) -> begin
(

let bs = (let _146_468 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1336 -> (match (_57_1336) with
| (_57_1334, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _146_468))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1342 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_483 = (FStar_Syntax_Subst.compress t)
in _146_483.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1348) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1353 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _146_488 = (let _146_487 = (let _146_486 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_486 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_487))
in (ml_or_tot _146_488 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1357 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_491 = (FStar_Syntax_Print.term_to_string head)
in (let _146_490 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_489 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_491 _146_490 _146_489))))
end else begin
()
end
in (

let _57_1359 = (let _146_492 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_492))
in (

let comp = (let _146_495 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1363 out -> (match (_57_1363) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _146_495))
in (let _146_497 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_496 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_497, comp, _146_496)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1372 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1372) with
| (bs, c) -> begin
(

let rec tc_args = (fun _57_1380 bs cres args -> (match (_57_1380) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1387))))::rest, ((_57_1395, None))::_57_1393) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1401 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1407 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1407) with
| (varg, _57_1405, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _146_506 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_506))
in (let _146_508 = (let _146_507 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_507, fvs))
in (tc_args _146_508 rest cres args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _57_1439 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1438 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1442 = x
in {FStar_Syntax_Syntax.ppname = _57_1442.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1442.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1445 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_509 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_509))
end else begin
()
end
in (

let _57_1447 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1450 = env
in {FStar_TypeChecker_Env.solver = _57_1450.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1450.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1450.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1450.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1450.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1450.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1450.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1450.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1450.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1450.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1450.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1450.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1450.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1450.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1450.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1450.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1450.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1450.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1450.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1450.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1453 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_512 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_511 = (FStar_Syntax_Print.term_to_string e)
in (let _146_510 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_512 _146_511 _146_510))))
end else begin
()
end
in (

let _57_1458 = (tc_term env e)
in (match (_57_1458) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _146_513 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_513 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _146_514 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_514 e))
in (

let _57_1465 = (((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g)
in (match (_57_1465) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_515 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_515)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _146_516 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_516))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((e.FStar_Syntax_Syntax.pos, Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_520 = (let _146_519 = (let _146_518 = (let _146_517 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_517))
in (_146_518)::arg_rets)
in (subst, (arg)::outargs, _146_519, ((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_520 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1469, []) -> begin
(

let _57_1472 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1492 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1482 -> (match (_57_1482) with
| (_57_1478, _57_1480, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _146_522 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_522 cres))
end else begin
(

let _57_1484 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_525 = (FStar_Syntax_Print.term_to_string head)
in (let _146_524 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_523 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_525 _146_524 _146_523))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1488 -> begin
(

let g = (let _146_526 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_526 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_531 = (let _146_530 = (let _146_529 = (let _146_528 = (let _146_527 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_527))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _146_528))
in (FStar_Syntax_Syntax.mk_Total _146_529))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_530))
in (_146_531, g)))
end)
in (match (_57_1492) with
| (cres, g) -> begin
(

let _57_1493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_532 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_532))
end else begin
()
end
in (

let comp = (FStar_List.fold_left (fun out _57_1499 -> (match (_57_1499) with
| (r1, x, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (x, out))
end)) cres comps)
in (

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let _57_1505 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1505) with
| (comp, g) -> begin
(app, comp, g)
end))))))
end)))
end
| ([], (arg)::_57_1508) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _146_540 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_540 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1520 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_541 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_541))
end else begin
()
end
in (let _146_545 = (let _146_544 = (let _146_543 = (let _146_542 = (FStar_TypeChecker_Env.get_range env)
in (_146_542, None, cres))
in (_146_543)::comps)
in (subst, outargs, arg_rets, _146_544, g, fvs))
in (tc_args _146_545 bs (FStar_Syntax_Util.lcomp_of_comp cres') args)))
end
| _57_1523 when (not (norm)) -> begin
(let _146_546 = (unfold_whnf env tres)
in (aux true _146_546))
end
| _57_1525 -> begin
(let _146_552 = (let _146_551 = (let _146_550 = (let _146_548 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_547 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_548 _146_547)))
in (let _146_549 = (FStar_Syntax_Syntax.argpos arg)
in (_146_550, _146_549)))
in FStar_Syntax_Syntax.Error (_146_551))
in (Prims.raise _146_552))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1527 -> begin
if (not (norm)) then begin
(let _146_553 = (unfold_whnf env tf)
in (check_function_app true _146_553))
end else begin
(let _146_556 = (let _146_555 = (let _146_554 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_554, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_555))
in (Prims.raise _146_556))
end
end))
in (let _146_558 = (let _146_557 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_557))
in (check_function_app false _146_558))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1563 = (FStar_List.fold_left2 (fun _57_1544 _57_1547 _57_1550 -> (match ((_57_1544, _57_1547, _57_1550)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1551 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1556 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1556) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _146_568 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_568 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_572 = (let _146_570 = (let _146_569 = (FStar_Syntax_Syntax.as_arg e)
in (_146_569)::[])
in (FStar_List.append seen _146_570))
in (let _146_571 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_572, _146_571, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1563) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _146_573 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_573 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1568 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1568) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1570 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1577 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1577) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1582 = branch
in (match (_57_1582) with
| (cpat, _57_1580, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1590 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1590) with
| (pat_bvs, exps, p) -> begin
(

let _57_1591 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_585 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_584 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_585 _146_584)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1597 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1597) with
| (env1, _57_1596) -> begin
(

let env1 = (

let _57_1598 = env1
in {FStar_TypeChecker_Env.solver = _57_1598.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1598.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1598.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1598.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1598.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1598.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1598.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1598.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1598.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1598.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1598.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1598.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1598.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1598.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1598.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1598.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1598.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1598.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1598.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1598.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1637 = (let _146_608 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1603 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_588 = (FStar_Syntax_Print.term_to_string e)
in (let _146_587 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_588 _146_587)))
end else begin
()
end
in (

let _57_1608 = (tc_term env1 e)
in (match (_57_1608) with
| (e, lc, g) -> begin
(

let _57_1609 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_590 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_589 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_590 _146_589)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1615 = (let _146_591 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1613 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1613.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1613.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1613.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_591 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _146_596 = (let _146_595 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_595 (FStar_List.map (fun _57_1623 -> (match (_57_1623) with
| (u, _57_1622) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_596 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1631 = if (let _146_597 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_597)) then begin
(

let unresolved = (let _146_598 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_598 FStar_Util.set_elements))
in (let _146_606 = (let _146_605 = (let _146_604 = (let _146_603 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_602 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_601 = (let _146_600 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1630 -> (match (_57_1630) with
| (u, _57_1629) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_600 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_603 _146_602 _146_601))))
in (_146_604, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_605))
in (Prims.raise _146_606)))
end else begin
()
end
in (

let _57_1633 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_607 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_607))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_608 FStar_List.unzip))
in (match (_57_1637) with
| (exps, norm_exps) -> begin
(

let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let _57_1644 = (let _146_609 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_609 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1644) with
| (scrutinee_env, _57_1643) -> begin
(

let _57_1650 = (tc_pat true pat_t pattern)
in (match (_57_1650) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1660 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1657 = (let _146_610 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_610 e))
in (match (_57_1657) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1660) with
| (when_clause, g_when) -> begin
(

let _57_1664 = (tc_term pat_env branch_exp)
in (match (_57_1664) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_612 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_611 -> Some (_146_611)) _146_612))
end)
in (

let _57_1720 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1682 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_616 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_615 -> Some (_146_615)) _146_616))
end))
end))) None))
in (

let _57_1690 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1690) with
| (c, g_branch) -> begin
(

let _57_1715 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _146_619 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_618 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_619, _146_618)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _146_620 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_620))
in (let _146_623 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_622 = (let _146_621 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_621 g_when))
in (_146_623, _146_622)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_624 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_624, g_when))))
end)
in (match (_57_1715) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_626 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_625 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_626, _146_625, g_branch))))
end))
end)))
in (match (_57_1720) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _146_636 = (let _146_635 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_635))
in (FStar_List.length _146_636)) > 1) then begin
(

let disc = (let _146_637 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_637 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _146_639 = (let _146_638 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_638)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_639 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_640 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_640)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1730 -> (match (()) with
| () -> begin
(let _146_646 = (let _146_645 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_644 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_643 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_645 _146_644 _146_643))))
in (FStar_All.failwith _146_646))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1737) -> begin
(head_constructor t)
end
| _57_1741 -> begin
(fail ())
end))
in (

let pat_exp = (let _146_649 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_649 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1766) -> begin
(let _146_654 = (let _146_653 = (let _146_652 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_651 = (let _146_650 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_650)::[])
in (_146_652)::_146_651))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_653 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_654)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_655 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_655))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _146_662 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1784 -> (match (_57_1784) with
| (ei, _57_1783) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1788 -> begin
(

let sub_term = (let _146_661 = (let _146_658 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_658 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_660 = (let _146_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_659)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_661 _146_660 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_662 FStar_List.flatten))
in (let _146_663 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_663 sub_term_guards)))
end)
end
| _57_1792 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _146_668 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_668))
in (

let _57_1800 = (FStar_Syntax_Util.type_u ())
in (match (_57_1800) with
| (k, _57_1799) -> begin
(

let _57_1806 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1806) with
| (t, _57_1803, _57_1805) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _146_669 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_669 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (

let _57_1814 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_670 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_670))
end else begin
()
end
in (let _146_671 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_671, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let _57_1831 = (check_let_bound_def true env lb)
in (match (_57_1831) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1843 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _146_674 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_674 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1838 = (let _146_678 = (let _146_677 = (let _146_676 = (let _146_675 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_675))
in (_146_676)::[])
in (FStar_TypeChecker_Util.generalize env _146_677))
in (FStar_List.hd _146_678))
in (match (_57_1838) with
| (_57_1834, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1843) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1853 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _57_1846 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1846) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1847 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _146_679 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_679 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_680 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_680, c1)))
end
end))
end else begin
(

let _57_1849 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_681 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_681)))
end
in (match (_57_1853) with
| (e2, c1) -> begin
(

let cres = (let _146_682 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_682))
in (

let _57_1855 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_683 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_683, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1859 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_1870 = env
in {FStar_TypeChecker_Env.solver = _57_1870.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1870.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1870.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1870.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1870.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1870.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1870.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1870.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1870.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1870.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1870.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1870.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1870.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1870.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1870.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1870.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1870.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1870.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1870.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1870.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1879 = (let _146_687 = (let _146_686 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_686 Prims.fst))
in (check_let_bound_def false _146_687 lb))
in (match (_57_1879) with
| (e1, _57_1875, c1, g1, annotated) -> begin
(

let x = (

let _57_1880 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1886 = (let _146_689 = (let _146_688 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_688)::[])
in (FStar_Syntax_Subst.open_term _146_689 e2))
in (match (_57_1886) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1892 = (let _146_690 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_690 e2))
in (match (_57_1892) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e = (let _146_693 = (let _146_692 = (let _146_691 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_691))
in FStar_Syntax_Syntax.Tm_let (_146_692))
in (FStar_Syntax_Syntax.mk _146_693 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let x_eq_e1 = (let _146_696 = (let _146_695 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_695 e1))
in (FStar_All.pipe_left (fun _146_694 -> FStar_TypeChecker_Common.NonTrivial (_146_694)) _146_696))
in (

let g2 = (let _146_698 = (let _146_697 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_697 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_698))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _146_699 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _146_699)) then begin
(e, cres, guard)
end else begin
(

let _57_1898 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1901 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1913 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1913) with
| (lbs, e2) -> begin
(

let _57_1916 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1916) with
| (env0, topt) -> begin
(

let _57_1919 = (build_let_rec_env true env0 lbs)
in (match (_57_1919) with
| (lbs, rec_env) -> begin
(

let _57_1922 = (check_let_recs rec_env lbs)
in (match (_57_1922) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _146_702 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_702 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _146_705 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_705 (fun _146_704 -> Some (_146_704))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _146_709 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_708 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_708)))))
in (FStar_TypeChecker_Util.generalize env _146_709))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1933 -> (match (_57_1933) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _146_711 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_711))
in (

let _57_1936 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1940 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1940) with
| (lbs, e2) -> begin
(let _146_713 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_712 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_713, cres, _146_712)))
end)))))))
end))
end))
end))
end))
end
| _57_1942 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1954 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1954) with
| (lbs, e2) -> begin
(

let _57_1957 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1957) with
| (env0, topt) -> begin
(

let _57_1960 = (build_let_rec_env false env0 lbs)
in (match (_57_1960) with
| (lbs, rec_env) -> begin
(

let _57_1963 = (check_let_recs rec_env lbs)
in (match (_57_1963) with
| (lbs, g_lbs) -> begin
(

let _57_1975 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1966 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1966.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1966.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_1969 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1969.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1969.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1969.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1969.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1975) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_1981 = (tc_term env e2)
in (match (_57_1981) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_1985 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1985.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1985.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1985.FStar_Syntax_Syntax.comp})
in (

let _57_1990 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1990) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1993) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_1996 = (check_no_escape None env bvs tres)
in (e, cres, guard))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| _57_1999 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2032 = (FStar_List.fold_left (fun _57_2006 lb -> (match (_57_2006) with
| (lbs, env) -> begin
(

let _57_2011 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2011) with
| (univ_vars, t, check_t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(

let _57_2020 = (let _146_725 = (let _146_724 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_724))
in (tc_check_tot_or_gtot_term (

let _57_2014 = env0
in {FStar_TypeChecker_Env.solver = _57_2014.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2014.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2014.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2014.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2014.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2014.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2014.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2014.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2014.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2014.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2014.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2014.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2014.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2014.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2014.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2014.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2014.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2014.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2014.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2014.FStar_TypeChecker_Env.use_bv_sorts}) t _146_725))
in (match (_57_2020) with
| (t, _57_2018, g) -> begin
(

let _57_2021 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _57_2024 = env
in {FStar_TypeChecker_Env.solver = _57_2024.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2024.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2024.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2024.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2024.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2024.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2024.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2024.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2024.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2024.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2024.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2024.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2024.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2024.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2024.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2024.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2024.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2024.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2024.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2024.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2027 = lb
in {FStar_Syntax_Syntax.lbname = _57_2027.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2027.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2032) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2045 = (let _146_730 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2039 = (let _146_729 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_729 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2039) with
| (e, c, g) -> begin
(

let _57_2040 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_730 FStar_List.unzip))
in (match (_57_2045) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2053 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2053) with
| (env1, _57_2052) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2059 = (check_lbtyp top_level env lb)
in (match (_57_2059) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2060 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2067 = (tc_maybe_toplevel_term (

let _57_2062 = env1
in {FStar_TypeChecker_Env.solver = _57_2062.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2062.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2062.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2062.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2062.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2062.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2062.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2062.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2062.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2062.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2062.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2062.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2062.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2062.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2062.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2062.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2062.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2062.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2062.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2062.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2067) with
| (e1, c1, g1) -> begin
(

let _57_2071 = (let _146_737 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2068 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_737 e1 c1 wf_annot))
in (match (_57_2071) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2073 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_738 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_738))
end else begin
()
end
in (let _146_739 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_739))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2080 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2083 -> begin
(

let _57_2086 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2086) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_743 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_743))
end else begin
(

let _57_2091 = (FStar_Syntax_Util.type_u ())
in (match (_57_2091) with
| (k, _57_2090) -> begin
(

let _57_2096 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2096) with
| (t, _57_2094, g) -> begin
(

let _57_2097 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_746 = (let _146_744 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_744))
in (let _146_745 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_746 _146_745)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _146_747 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_747))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2103 -> (match (_57_2103) with
| (x, imp) -> begin
(

let _57_2106 = (FStar_Syntax_Util.type_u ())
in (match (_57_2106) with
| (tu, u) -> begin
(

let _57_2111 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2111) with
| (t, _57_2109, g) -> begin
(

let x = ((

let _57_2112 = x
in {FStar_Syntax_Syntax.ppname = _57_2112.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2112.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2115 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_751 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_750 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_751 _146_750)))
end else begin
()
end
in (let _146_752 = (maybe_push_binding env x)
in (x, _146_752, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| (b)::bs -> begin
(

let _57_2130 = (tc_binder env b)
in (match (_57_2130) with
| (b, env', g, u) -> begin
(

let _57_2135 = (aux env' bs)
in (match (_57_2135) with
| (bs, env', g', us) -> begin
(let _146_760 = (let _146_759 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_759))
in ((b)::bs, env', _146_760, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2143 _57_2146 -> (match ((_57_2143, _57_2146)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2151 = (tc_term env t)
in (match (_57_2151) with
| (t, _57_2149, g') -> begin
(let _146_769 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_769))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2155 -> (match (_57_2155) with
| (pats, g) -> begin
(

let _57_2158 = (tc_args env p)
in (match (_57_2158) with
| (args, g') -> begin
(let _146_772 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_772))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2164 = (tc_maybe_toplevel_term env e)
in (match (_57_2164) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2167 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_775 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_775))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2172 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_776 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_776, false))
end else begin
(let _146_777 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_777, true))
end
in (match (_57_2172) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_778 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_778))
end
| _57_2176 -> begin
if allow_ghost then begin
(let _146_781 = (let _146_780 = (let _146_779 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_779, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_780))
in (Prims.raise _146_781))
end else begin
(let _146_784 = (let _146_783 = (let _146_782 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_782, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_783))
in (Prims.raise _146_784))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2186 = (tc_tot_or_gtot_term env t)
in (match (_57_2186) with
| (t, c, g) -> begin
(

let _57_2187 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2195 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2195) with
| (t, c, g) -> begin
(

let _57_2196 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_804 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_804)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _146_808 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_808))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2211 = (tc_binders env tps)
in (match (_57_2211) with
| (tps, env, g, us) -> begin
(

let _57_2212 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2218 -> (match (()) with
| () -> begin
(let _146_823 = (let _146_822 = (let _146_821 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_821, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_822))
in (Prims.raise _146_823))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2231))::((wp, _57_2227))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2235 -> begin
(fail ())
end))
end
| _57_2237 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2244 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2244) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2246 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2250 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2250) with
| (uvs, t') -> begin
(match ((let _146_830 = (FStar_Syntax_Subst.compress t')
in _146_830.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2256 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _146_841 = (let _146_840 = (let _146_839 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_839, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_840))
in (Prims.raise _146_841)))
in (match ((let _146_842 = (FStar_Syntax_Subst.compress signature)
in _146_842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2273))::((wp, _57_2269))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2277 -> begin
(fail signature)
end))
end
| _57_2279 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2284 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2284) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2287 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2291 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2295 = ed
in (let _146_859 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_858 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_857 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_856 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_855 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_854 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_853 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_852 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_851 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_850 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_849 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2295.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2295.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2295.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2295.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2295.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_859; FStar_Syntax_Syntax.bind_wp = _146_858; FStar_Syntax_Syntax.if_then_else = _146_857; FStar_Syntax_Syntax.ite_wp = _146_856; FStar_Syntax_Syntax.wp_binop = _146_855; FStar_Syntax_Syntax.wp_as_type = _146_854; FStar_Syntax_Syntax.close_wp = _146_853; FStar_Syntax_Syntax.assert_p = _146_852; FStar_Syntax_Syntax.assume_p = _146_851; FStar_Syntax_Syntax.null_wp = _146_850; FStar_Syntax_Syntax.trivial = _146_849}))))))))))))))
end)
in (ed, a, wp))
end)))


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let normalize_and_make_binders_explicit = (fun tm -> (

let tm = (normalize tm)
in (

let rec visit_term = (fun tm -> (

let n = (match ((let _146_881 = (FStar_Syntax_Subst.compress tm)
in _146_881.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let comp = (visit_comp comp)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(

let comp = (visit_maybe_lcomp comp)
in (

let term = (visit_term term)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2330 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2332 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2332.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2332.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2332.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2336 -> (match (_57_2336) with
| (bv, a) -> begin
(let _146_885 = (

let _57_2337 = bv
in (let _146_883 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2337.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2337.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_883}))
in (let _146_884 = (FStar_Syntax_Syntax.as_implicit false)
in (_146_885, _146_884)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _146_890 = (let _146_889 = (let _146_888 = (let _146_887 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _146_887))
in (FStar_Syntax_Util.lcomp_of_comp _146_888))
in FStar_Util.Inl (_146_889))
in Some (_146_890))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _146_892 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_146_892))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _146_893 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_146_893))
end
| comp -> begin
comp
end)
in (

let _57_2351 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2351.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2351.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2351.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2356 -> (match (_57_2356) with
| (tm, q) -> begin
(let _146_896 = (visit_term tm)
in (_146_896, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2360 = (let _146_901 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _146_901))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2375 = (tc_term env t)
in (match (_57_2375) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2371; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2368; FStar_Syntax_Syntax.comp = _57_2366}, _57_2374) -> begin
(

let _57_2376 = (let _146_904 = (let _146_903 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _146_903))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _146_904))
in (let _146_906 = (let _146_905 = (normalize e)
in (FStar_Syntax_Print.term_to_string _146_905))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _146_906)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _146_909 = (FStar_Syntax_Subst.compress t)
in _146_909.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2387 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _146_910 = (collect_binders rest)
in (FStar_List.append bs _146_910)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2390) -> begin
[]
end
| _57_2393 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2408 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _146_917 = (normalize wp_a)
in (collect_binders _146_917))
in ((fun t -> (let _146_923 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _146_923))), (fun t -> (let _146_926 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _146_926))), (fun _57_2398 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2402 -> (match (_57_2402) with
| (bv, _57_2401) -> begin
(

let _57_2403 = (let _146_930 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _146_930))
in (let _146_933 = (let _146_932 = (let _146_931 = (FStar_ST.read i)
in (FStar_Util.string_of_int _146_931))
in (Prims.strcat "g" _146_932))
in (FStar_Syntax_Syntax.gen_bv _146_933 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2408) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2411 -> (match (_57_2411) with
| (t, b) -> begin
(let _146_939 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _146_939))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _146_942 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _146_942))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _146_945 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_945))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _146_946 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _146_946))
in (

let ret = (let _146_951 = (let _146_950 = (let _146_949 = (let _146_948 = (let _146_947 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _146_947))
in (FStar_Syntax_Syntax.mk_Total _146_948))
in (FStar_Syntax_Util.lcomp_of_comp _146_949))
in FStar_Util.Inl (_146_950))
in Some (_146_951))
in (

let gamma = (mk_gamma ())
in (

let body = (let _146_953 = (implicit_binders_of_list gamma)
in (let _146_952 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _146_953 _146_952 ret)))
in (let _146_954 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _146_954 body ret)))))))
in (

let _57_2423 = (let _146_958 = (let _146_957 = (let _146_956 = (let _146_955 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_955)::[])
in (FStar_List.append binders _146_956))
in (FStar_Syntax_Util.abs _146_957 c_pure None))
in (check "pure" _146_958))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _146_966 = (let _146_965 = (let _146_964 = (let _146_961 = (let _146_960 = (let _146_959 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _146_959))
in (FStar_Syntax_Syntax.mk_binder _146_960))
in (_146_961)::[])
in (let _146_963 = (let _146_962 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_962))
in (FStar_Syntax_Util.arrow _146_964 _146_963)))
in (mk_gctx _146_965))
in (FStar_Syntax_Syntax.gen_bv "l" None _146_966))
in (

let r = (let _146_968 = (let _146_967 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_967))
in (FStar_Syntax_Syntax.gen_bv "r" None _146_968))
in (

let ret = (let _146_973 = (let _146_972 = (let _146_971 = (let _146_970 = (let _146_969 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_969))
in (FStar_Syntax_Syntax.mk_Total _146_970))
in (FStar_Syntax_Util.lcomp_of_comp _146_971))
in FStar_Util.Inl (_146_972))
in Some (_146_973))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _146_979 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_978 = (let _146_977 = (let _146_976 = (let _146_975 = (let _146_974 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _146_974 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _146_975))
in (_146_976)::[])
in (FStar_List.append gamma_as_args _146_977))
in (FStar_Syntax_Util.mk_app _146_979 _146_978)))
in (let _146_980 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _146_980 inner_body ret)))))
in (let _146_981 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _146_981 outer_body ret))))))))
in (

let _57_2435 = (let _146_985 = (let _146_984 = (let _146_983 = (let _146_982 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_982)::[])
in (FStar_List.append binders _146_983))
in (FStar_Syntax_Util.abs _146_984 c_app None))
in (check "app" _146_985))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_990 = (let _146_987 = (let _146_986 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_986))
in (_146_987)::[])
in (let _146_989 = (let _146_988 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_988))
in (FStar_Syntax_Util.arrow _146_990 _146_989)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _146_992 = (let _146_991 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_991))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_992))
in (

let ret = (let _146_997 = (let _146_996 = (let _146_995 = (let _146_994 = (let _146_993 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_993))
in (FStar_Syntax_Syntax.mk_Total _146_994))
in (FStar_Syntax_Util.lcomp_of_comp _146_995))
in FStar_Util.Inl (_146_996))
in Some (_146_997))
in (let _146_1010 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _146_1009 = (let _146_1008 = (let _146_1007 = (let _146_1006 = (let _146_1005 = (let _146_1004 = (let _146_1001 = (let _146_1000 = (let _146_999 = (let _146_998 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_998)::[])
in (unknown)::_146_999)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1000))
in (FStar_Syntax_Util.mk_app c_pure _146_1001))
in (let _146_1003 = (let _146_1002 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1002)::[])
in (_146_1004)::_146_1003))
in (unknown)::_146_1005)
in (unknown)::_146_1006)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1007))
in (FStar_Syntax_Util.mk_app c_app _146_1008))
in (FStar_Syntax_Util.abs _146_1010 _146_1009 ret)))))))))
in (

let _57_2445 = (let _146_1014 = (let _146_1013 = (let _146_1012 = (let _146_1011 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1011)::[])
in (FStar_List.append binders _146_1012))
in (FStar_Syntax_Util.abs _146_1013 c_lift1 None))
in (check "lift1" _146_1014))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_1022 = (let _146_1019 = (let _146_1015 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1015))
in (let _146_1018 = (let _146_1017 = (let _146_1016 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _146_1016))
in (_146_1017)::[])
in (_146_1019)::_146_1018))
in (let _146_1021 = (let _146_1020 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _146_1020))
in (FStar_Syntax_Util.arrow _146_1022 _146_1021)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _146_1024 = (let _146_1023 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1023))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1024))
in (

let a2 = (let _146_1026 = (let _146_1025 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1025))
in (FStar_Syntax_Syntax.gen_bv "a2" None _146_1026))
in (

let ret = (let _146_1031 = (let _146_1030 = (let _146_1029 = (let _146_1028 = (let _146_1027 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _146_1027))
in (FStar_Syntax_Syntax.mk_Total _146_1028))
in (FStar_Syntax_Util.lcomp_of_comp _146_1029))
in FStar_Util.Inl (_146_1030))
in Some (_146_1031))
in (let _146_1051 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _146_1050 = (let _146_1049 = (let _146_1048 = (let _146_1047 = (let _146_1046 = (let _146_1045 = (let _146_1042 = (let _146_1041 = (let _146_1040 = (let _146_1039 = (let _146_1038 = (let _146_1035 = (let _146_1034 = (let _146_1033 = (let _146_1032 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1032)::[])
in (unknown)::_146_1033)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1034))
in (FStar_Syntax_Util.mk_app c_pure _146_1035))
in (let _146_1037 = (let _146_1036 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1036)::[])
in (_146_1038)::_146_1037))
in (unknown)::_146_1039)
in (unknown)::_146_1040)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1041))
in (FStar_Syntax_Util.mk_app c_app _146_1042))
in (let _146_1044 = (let _146_1043 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_146_1043)::[])
in (_146_1045)::_146_1044))
in (unknown)::_146_1046)
in (unknown)::_146_1047)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1048))
in (FStar_Syntax_Util.mk_app c_app _146_1049))
in (FStar_Syntax_Util.abs _146_1051 _146_1050 ret)))))))))))
in (

let _57_2456 = (let _146_1055 = (let _146_1054 = (let _146_1053 = (let _146_1052 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1052)::[])
in (FStar_List.append binders _146_1053))
in (FStar_Syntax_Util.abs _146_1054 c_lift2 None))
in (check "lift2" _146_1055))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_1061 = (let _146_1057 = (let _146_1056 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1056))
in (_146_1057)::[])
in (let _146_1060 = (let _146_1059 = (let _146_1058 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1058))
in (FStar_Syntax_Syntax.mk_Total _146_1059))
in (FStar_Syntax_Util.arrow _146_1061 _146_1060)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _146_1071 = (let _146_1070 = (let _146_1069 = (let _146_1068 = (let _146_1067 = (let _146_1066 = (let _146_1063 = (let _146_1062 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1062))
in (_146_1063)::[])
in (let _146_1065 = (let _146_1064 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_1064))
in (FStar_Syntax_Util.arrow _146_1066 _146_1065)))
in (mk_ctx _146_1067))
in (FStar_Syntax_Syntax.mk_Total _146_1068))
in (FStar_Syntax_Util.lcomp_of_comp _146_1069))
in FStar_Util.Inl (_146_1070))
in Some (_146_1071))
in (

let e1 = (let _146_1072 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _146_1072))
in (

let gamma = (mk_gamma ())
in (

let body = (let _146_1082 = (let _146_1075 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _146_1074 = (let _146_1073 = (FStar_Syntax_Syntax.mk_binder e1)
in (_146_1073)::[])
in (FStar_List.append _146_1075 _146_1074)))
in (let _146_1081 = (let _146_1080 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _146_1079 = (let _146_1078 = (let _146_1076 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _146_1076))
in (let _146_1077 = (args_of_bv gamma)
in (_146_1078)::_146_1077))
in (FStar_Syntax_Util.mk_app _146_1080 _146_1079)))
in (FStar_Syntax_Util.abs _146_1082 _146_1081 ret)))
in (let _146_1083 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _146_1083 body ret))))))))))
in (

let _57_2467 = (let _146_1087 = (let _146_1086 = (let _146_1085 = (let _146_1084 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1084)::[])
in (FStar_List.append binders _146_1085))
in (FStar_Syntax_Util.abs _146_1086 c_push None))
in (check "push" _146_1087))
in (

let ret_tot_wp_a = (let _146_1090 = (let _146_1089 = (let _146_1088 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _146_1088))
in FStar_Util.Inl (_146_1089))
in Some (_146_1090))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _146_1101 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _146_1100 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _146_1099 = (let _146_1098 = (let _146_1097 = (let _146_1096 = (let _146_1095 = (let _146_1094 = (let _146_1093 = (let _146_1092 = (let _146_1091 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _146_1091))
in (_146_1092)::[])
in (FStar_Syntax_Util.mk_app l_ite _146_1093))
in (_146_1094)::[])
in (unknown)::_146_1095)
in (unknown)::_146_1096)
in (unknown)::_146_1097)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1098))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1099)))
in (FStar_Syntax_Util.abs _146_1101 _146_1100 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2474 = (let _146_1102 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _146_1102))
in (

let wp_binop = (

let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (

let op = (let _146_1108 = (let _146_1107 = (let _146_1105 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _146_1104 = (let _146_1103 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_146_1103)::[])
in (_146_1105)::_146_1104))
in (let _146_1106 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_1107 _146_1106)))
in (FStar_Syntax_Syntax.gen_bv "op" None _146_1108))
in (

let r = (FStar_Syntax_Syntax.gen_bv "r" None wp_a)
in (let _146_1120 = (FStar_Syntax_Syntax.binders_of_list ((a)::(l)::(op)::(r)::[]))
in (let _146_1119 = (let _146_1118 = (let _146_1117 = (let _146_1116 = (let _146_1115 = (let _146_1114 = (let _146_1113 = (FStar_Syntax_Syntax.bv_to_name op)
in (let _146_1112 = (let _146_1111 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_1110 = (let _146_1109 = (FStar_Syntax_Syntax.bv_to_name r)
in (_146_1109)::[])
in (_146_1111)::_146_1110))
in (_146_1113)::_146_1112))
in (unknown)::_146_1114)
in (unknown)::_146_1115)
in (unknown)::_146_1116)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1117))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1118))
in (FStar_Syntax_Util.abs _146_1120 _146_1119 ret_tot_wp_a))))))
in (

let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (

let _57_2481 = (let _146_1121 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _146_1121))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _146_1135 = (let _146_1134 = (let _146_1133 = (let _146_1132 = (let _146_1131 = (let _146_1128 = (let _146_1127 = (let _146_1126 = (let _146_1125 = (let _146_1124 = (let _146_1123 = (let _146_1122 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1122))
in (_146_1123)::[])
in (FStar_Syntax_Util.mk_app l_and _146_1124))
in (_146_1125)::[])
in (unknown)::_146_1126)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1127))
in (FStar_Syntax_Util.mk_app c_pure _146_1128))
in (let _146_1130 = (let _146_1129 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1129)::[])
in (_146_1131)::_146_1130))
in (unknown)::_146_1132)
in (unknown)::_146_1133)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1134))
in (FStar_Syntax_Util.mk_app c_app _146_1135))
in (let _146_1136 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1136 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2489 = (let _146_1137 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _146_1137))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _146_1151 = (let _146_1150 = (let _146_1149 = (let _146_1148 = (let _146_1147 = (let _146_1144 = (let _146_1143 = (let _146_1142 = (let _146_1141 = (let _146_1140 = (let _146_1139 = (let _146_1138 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1138))
in (_146_1139)::[])
in (FStar_Syntax_Util.mk_app l_imp _146_1140))
in (_146_1141)::[])
in (unknown)::_146_1142)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1143))
in (FStar_Syntax_Util.mk_app c_pure _146_1144))
in (let _146_1146 = (let _146_1145 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1145)::[])
in (_146_1147)::_146_1146))
in (unknown)::_146_1148)
in (unknown)::_146_1149)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1150))
in (FStar_Syntax_Util.mk_app c_app _146_1151))
in (let _146_1152 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1152 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2497 = (let _146_1153 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _146_1153))
in (

let tforall = (let _146_1156 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1155 = (let _146_1154 = (FStar_Syntax_Syntax.as_arg unknown)
in (_146_1154)::[])
in (FStar_Syntax_Util.mk_app _146_1156 _146_1155)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_1160 = (let _146_1158 = (let _146_1157 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1157))
in (_146_1158)::[])
in (let _146_1159 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1160 _146_1159)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _146_1173 = (let _146_1172 = (let _146_1171 = (let _146_1170 = (let _146_1169 = (let _146_1161 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _146_1161))
in (let _146_1168 = (let _146_1167 = (let _146_1166 = (let _146_1165 = (let _146_1164 = (let _146_1163 = (let _146_1162 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1162)::[])
in (unknown)::_146_1163)
in (unknown)::_146_1164)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1165))
in (FStar_Syntax_Util.mk_app c_push _146_1166))
in (_146_1167)::[])
in (_146_1169)::_146_1168))
in (unknown)::_146_1170)
in (unknown)::_146_1171)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1172))
in (FStar_Syntax_Util.mk_app c_app _146_1173))
in (let _146_1174 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _146_1174 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2506 = (let _146_1175 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _146_1175))
in (

let ret_tot_type0 = (let _146_1178 = (let _146_1177 = (let _146_1176 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1176))
in FStar_Util.Inl (_146_1177))
in Some (_146_1178))
in (

let mk_forall = (fun x body -> (

let tforall = (let _146_1185 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1184 = (let _146_1183 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_146_1183)::[])
in (FStar_Syntax_Util.mk_app _146_1185 _146_1184)))
in (let _146_1192 = (let _146_1191 = (let _146_1190 = (let _146_1189 = (let _146_1188 = (let _146_1187 = (let _146_1186 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_1186)::[])
in (FStar_Syntax_Util.abs _146_1187 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _146_1188))
in (_146_1189)::[])
in (tforall, _146_1190))
in FStar_Syntax_Syntax.Tm_app (_146_1191))
in (FStar_Syntax_Syntax.mk _146_1192 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _146_1200 = (let _146_1199 = (FStar_Syntax_Subst.compress t)
in (normalize _146_1199))
in _146_1200.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2518) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _146_1212 = (let _146_1202 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _146_1201 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _146_1202 _146_1201)))
in (let _146_1211 = (let _146_1210 = (let _146_1205 = (let _146_1204 = (let _146_1203 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _146_1203))
in (_146_1204)::[])
in (FStar_Syntax_Util.mk_app x _146_1205))
in (let _146_1209 = (let _146_1208 = (let _146_1207 = (let _146_1206 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _146_1206))
in (_146_1207)::[])
in (FStar_Syntax_Util.mk_app y _146_1208))
in (mk_leq b _146_1210 _146_1209)))
in (FStar_Syntax_Util.mk_imp _146_1212 _146_1211)))
in (let _146_1213 = (mk_forall a2 body)
in (mk_forall a1 _146_1213))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_2554 = t
in (let _146_1217 = (let _146_1216 = (let _146_1215 = (let _146_1214 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _146_1214))
in ((binder)::[], _146_1215))
in FStar_Syntax_Syntax.Tm_arrow (_146_1216))
in {FStar_Syntax_Syntax.n = _146_1217; FStar_Syntax_Syntax.tk = _57_2554.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2554.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2554.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2558) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2561 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _146_1219 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _146_1218 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _146_1219 _146_1218)))
in (let _146_1220 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _146_1220 body ret_tot_type0)))))
in (

let _57_2566 = (let _146_1224 = (let _146_1223 = (let _146_1222 = (let _146_1221 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1221)::[])
in (FStar_List.append binders _146_1222))
in (FStar_Syntax_Util.abs _146_1223 stronger None))
in (check "stronger" _146_1224))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _146_1232 = (let _146_1231 = (let _146_1230 = (let _146_1227 = (let _146_1226 = (let _146_1225 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _146_1225))
in (_146_1226)::[])
in (FStar_Syntax_Util.mk_app null_wp _146_1227))
in (let _146_1229 = (let _146_1228 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1228)::[])
in (_146_1230)::_146_1229))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1231))
in (FStar_Syntax_Util.mk_app stronger _146_1232))
in (let _146_1233 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1233 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2573 = (let _146_1234 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _146_1234))
in (

let _57_2575 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2575.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2575.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2575.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2575.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2575.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2575.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2575.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2575.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2575.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2575.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2580 = ()
in (

let _57_2584 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2584) with
| (binders_un, signature_un) -> begin
(

let _57_2589 = (tc_tparams env0 binders_un)
in (match (_57_2589) with
| (binders, env, _57_2588) -> begin
(

let _57_2593 = (tc_trivial_guard env signature_un)
in (match (_57_2593) with
| (signature, _57_2592) -> begin
(

let ed = (

let _57_2594 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2594.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2594.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2594.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2594.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2594.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2594.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2594.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.wp_binop = _57_2594.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2594.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2594.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2594.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2594.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2594.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2594.FStar_Syntax_Syntax.trivial})
in (

let _57_2600 = (open_effect_decl env ed)
in (match (_57_2600) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2602 -> (match (()) with
| () -> begin
(

let _57_2606 = (tc_trivial_guard env signature_un)
in (match (_57_2606) with
| (signature, _57_2605) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _146_1243 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_1243))
in (

let _57_2608 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_1246 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_1245 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_1244 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _146_1246 _146_1245 _146_1244))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2615 k -> (match (_57_2615) with
| (_57_2613, t) -> begin
(check_and_gen env t k)
end))
in (

let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (

let ret = (

let expected_k = (let _146_1258 = (let _146_1256 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1255 = (let _146_1254 = (let _146_1253 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1253))
in (_146_1254)::[])
in (_146_1256)::_146_1255))
in (let _146_1257 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_1258 _146_1257)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let _57_2624 = (get_effect_signature ())
in (match (_57_2624) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _146_1262 = (let _146_1260 = (let _146_1259 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1259))
in (_146_1260)::[])
in (let _146_1261 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1262 _146_1261)))
in (

let expected_k = (let _146_1273 = (let _146_1271 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1270 = (let _146_1269 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1268 = (let _146_1267 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1266 = (let _146_1265 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1264 = (let _146_1263 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_146_1263)::[])
in (_146_1265)::_146_1264))
in (_146_1267)::_146_1266))
in (_146_1269)::_146_1268))
in (_146_1271)::_146_1270))
in (let _146_1272 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1273 _146_1272)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _146_1275 = (let _146_1274 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1274 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1275))
in (

let expected_k = (let _146_1284 = (let _146_1282 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1281 = (let _146_1280 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_1279 = (let _146_1278 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1277 = (let _146_1276 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1276)::[])
in (_146_1278)::_146_1277))
in (_146_1280)::_146_1279))
in (_146_1282)::_146_1281))
in (let _146_1283 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1284 _146_1283)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _146_1289 = (let _146_1287 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1286 = (let _146_1285 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1285)::[])
in (_146_1287)::_146_1286))
in (let _146_1288 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1289 _146_1288)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let wp_binop = (

let bin_op = (

let _57_2635 = (FStar_Syntax_Util.type_u ())
in (match (_57_2635) with
| (t1, u1) -> begin
(

let _57_2638 = (FStar_Syntax_Util.type_u ())
in (match (_57_2638) with
| (t2, u2) -> begin
(

let t = (let _146_1290 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_1290))
in (let _146_1295 = (let _146_1293 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_1292 = (let _146_1291 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_1291)::[])
in (_146_1293)::_146_1292))
in (let _146_1294 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1295 _146_1294))))
end))
end))
in (

let expected_k = (let _146_1304 = (let _146_1302 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1301 = (let _146_1300 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1299 = (let _146_1298 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_1297 = (let _146_1296 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1296)::[])
in (_146_1298)::_146_1297))
in (_146_1300)::_146_1299))
in (_146_1302)::_146_1301))
in (let _146_1303 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1304 _146_1303)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (

let wp_as_type = (

let _57_2646 = (FStar_Syntax_Util.type_u ())
in (match (_57_2646) with
| (t, _57_2645) -> begin
(

let expected_k = (let _146_1309 = (let _146_1307 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1306 = (let _146_1305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1305)::[])
in (_146_1307)::_146_1306))
in (let _146_1308 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_1309 _146_1308)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (

let close_wp = (

let b = (let _146_1311 = (let _146_1310 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1310 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1311))
in (

let b_wp_a = (let _146_1315 = (let _146_1313 = (let _146_1312 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1312))
in (_146_1313)::[])
in (let _146_1314 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1315 _146_1314)))
in (

let expected_k = (let _146_1322 = (let _146_1320 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1319 = (let _146_1318 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1317 = (let _146_1316 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_1316)::[])
in (_146_1318)::_146_1317))
in (_146_1320)::_146_1319))
in (let _146_1321 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1322 _146_1321)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _146_1331 = (let _146_1329 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1328 = (let _146_1327 = (let _146_1324 = (let _146_1323 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1323 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1324))
in (let _146_1326 = (let _146_1325 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1325)::[])
in (_146_1327)::_146_1326))
in (_146_1329)::_146_1328))
in (let _146_1330 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1331 _146_1330)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _146_1340 = (let _146_1338 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1337 = (let _146_1336 = (let _146_1333 = (let _146_1332 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1332 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1333))
in (let _146_1335 = (let _146_1334 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1334)::[])
in (_146_1336)::_146_1335))
in (_146_1338)::_146_1337))
in (let _146_1339 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1340 _146_1339)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _146_1343 = (let _146_1341 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1341)::[])
in (let _146_1342 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1343 _146_1342)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2662 = (FStar_Syntax_Util.type_u ())
in (match (_57_2662) with
| (t, _57_2661) -> begin
(

let expected_k = (let _146_1348 = (let _146_1346 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1345 = (let _146_1344 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1344)::[])
in (_146_1346)::_146_1345))
in (let _146_1347 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1348 _146_1347)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _146_1349 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1349))
in (

let _57_2668 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2668) with
| (univs, t) -> begin
(

let _57_2684 = (match ((let _146_1351 = (let _146_1350 = (FStar_Syntax_Subst.compress t)
in _146_1350.FStar_Syntax_Syntax.n)
in (binders, _146_1351))) with
| ([], _57_2671) -> begin
([], t)
end
| (_57_2674, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2681 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2684) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _146_1356 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1356))
in (

let _57_2689 = ()
in ts)))
in (

let ed = (

let _57_2691 = ed
in (let _146_1367 = (close 0 ret)
in (let _146_1366 = (close 1 bind_wp)
in (let _146_1365 = (close 0 if_then_else)
in (let _146_1364 = (close 0 ite_wp)
in (let _146_1363 = (close 0 wp_binop)
in (let _146_1362 = (close 0 wp_as_type)
in (let _146_1361 = (close 1 close_wp)
in (let _146_1360 = (close 0 assert_p)
in (let _146_1359 = (close 0 assume_p)
in (let _146_1358 = (close 0 null_wp)
in (let _146_1357 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2691.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2691.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1367; FStar_Syntax_Syntax.bind_wp = _146_1366; FStar_Syntax_Syntax.if_then_else = _146_1365; FStar_Syntax_Syntax.ite_wp = _146_1364; FStar_Syntax_Syntax.wp_binop = _146_1363; FStar_Syntax_Syntax.wp_as_type = _146_1362; FStar_Syntax_Syntax.close_wp = _146_1361; FStar_Syntax_Syntax.assert_p = _146_1360; FStar_Syntax_Syntax.assume_p = _146_1359; FStar_Syntax_Syntax.null_wp = _146_1358; FStar_Syntax_Syntax.trivial = _146_1357}))))))))))))
in (

let _57_2694 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1368 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1368))
end else begin
()
end
in ed)))
end))
end)))))))))))))))))))
end)))
end))
end))
end))))


let tc_lex_t = (fun env ses quals lids -> (

let _57_2700 = ()
in (

let _57_2708 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2737, _57_2739, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2728, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2717, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (let _146_1376 = (let _146_1375 = (let _146_1374 = (let _146_1373 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1373 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1374, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1375))
in (FStar_Syntax_Syntax.mk _146_1376 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _146_1377 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1377))
in (

let hd = (let _146_1378 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1378))
in (

let tl = (let _146_1383 = (let _146_1382 = (let _146_1381 = (let _146_1380 = (let _146_1379 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1379 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1380, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1381))
in (FStar_Syntax_Syntax.mk _146_1382 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1383))
in (

let res = (let _146_1387 = (let _146_1386 = (let _146_1385 = (let _146_1384 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1384 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1385, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1386))
in (FStar_Syntax_Syntax.mk _146_1387 None r2))
in (let _146_1388 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1388))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1390 = (let _146_1389 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1389))
in FStar_Syntax_Syntax.Sig_bundle (_146_1390)))))))))))))))
end
| _57_2763 -> begin
(let _146_1392 = (let _146_1391 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1391))
in (FStar_All.failwith _146_1392))
end))))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_2773 = (FStar_Syntax_Util.type_u ())
in (match (_57_2773) with
| (k, _57_2772) -> begin
(

let phi = (let _146_1403 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1403 (norm env)))
in (

let _57_2775 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _146_1417 = (let _146_1416 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1416))
in (FStar_TypeChecker_Errors.diag r _146_1417)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_2798 = ()
in (

let _57_2800 = (warn_positivity tc r)
in (

let _57_2804 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2804) with
| (tps, k) -> begin
(

let _57_2808 = (tc_tparams env tps)
in (match (_57_2808) with
| (tps, env_tps, us) -> begin
(

let _57_2811 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2811) with
| (indices, t) -> begin
(

let _57_2815 = (tc_tparams env_tps indices)
in (match (_57_2815) with
| (indices, env', us') -> begin
(

let _57_2819 = (tc_trivial_guard env' t)
in (match (_57_2819) with
| (t, _57_2818) -> begin
(

let k = (let _146_1422 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1422))
in (

let _57_2823 = (FStar_Syntax_Util.type_u ())
in (match (_57_2823) with
| (t_type, u) -> begin
(

let _57_2824 = (let _146_1423 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1423))
in (

let t_tc = (let _146_1424 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1424))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1425 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1425, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2831 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_2833 l -> ())
in (

let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_2850 = ()
in (

let _57_2885 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2854 -> (match (_57_2854) with
| (se, u_tc) -> begin
if (let _146_1438 = (let _146_1437 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1437))
in (FStar_Ident.lid_equals tc_lid _146_1438)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2856, _57_2858, tps, _57_2861, _57_2863, _57_2865, _57_2867, _57_2869) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2875 -> (match (_57_2875) with
| (x, _57_2874) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2877 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
end else begin
None
end
end)))
in (match (tps_u_opt) with
| Some (x) -> begin
x
end
| None -> begin
if (FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid) then begin
([], FStar_Syntax_Syntax.U_zero)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected data constructor", r))))
end
end))
in (match (_57_2885) with
| (tps, u_tc) -> begin
(

let _57_2905 = (match ((let _146_1440 = (FStar_Syntax_Subst.compress t)
in _146_1440.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2893 = (FStar_Util.first_N ntps bs)
in (match (_57_2893) with
| (_57_2891, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2899 -> (match (_57_2899) with
| (x, _57_2898) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _146_1443 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _146_1443))))
end))
end
| _57_2902 -> begin
([], t)
end)
in (match (_57_2905) with
| (arguments, result) -> begin
(

let _57_2906 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1446 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1445 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1444 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1446 _146_1445 _146_1444))))
end else begin
()
end
in (

let _57_2911 = (tc_tparams env arguments)
in (match (_57_2911) with
| (arguments, env', us) -> begin
(

let _57_2915 = (tc_trivial_guard env' result)
in (match (_57_2915) with
| (result, _57_2914) -> begin
(

let _57_2919 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2919) with
| (head, _57_2918) -> begin
(

let _57_2924 = (match ((let _146_1447 = (FStar_Syntax_Subst.compress head)
in _146_1447.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2923 -> begin
(let _146_1451 = (let _146_1450 = (let _146_1449 = (let _146_1448 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1448))
in (_146_1449, r))
in FStar_Syntax_Syntax.Error (_146_1450))
in (Prims.raise _146_1451))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2930 u_x -> (match (_57_2930) with
| (x, _57_2929) -> begin
(

let _57_2932 = ()
in (let _146_1455 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1455)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _146_1459 = (let _146_1457 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2938 -> (match (_57_2938) with
| (x, _57_2937) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1457 arguments))
in (let _146_1458 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1459 _146_1458)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2941 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_2947 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2951, _57_2953, tps, k, _57_2957, _57_2959, _57_2961, _57_2963) -> begin
(let _146_1470 = (let _146_1469 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1469))
in (FStar_Syntax_Syntax.null_binder _146_1470))
end
| _57_2967 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2971, _57_2973, t, _57_2976, _57_2978, _57_2980, _57_2982, _57_2984) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2988 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _146_1472 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1472))
in (

let _57_2991 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1473 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1473))
end else begin
()
end
in (

let _57_2995 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2995) with
| (uvs, t) -> begin
(

let _57_2997 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1477 = (let _146_1475 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1475 (FStar_String.concat ", ")))
in (let _146_1476 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1477 _146_1476)))
end else begin
()
end
in (

let _57_3001 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3001) with
| (uvs, t) -> begin
(

let _57_3005 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3005) with
| (args, _57_3004) -> begin
(

let _57_3008 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3008) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_3012 se -> (match (_57_3012) with
| (x, _57_3011) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3016, tps, _57_3019, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_3042 = (match ((let _146_1480 = (FStar_Syntax_Subst.compress ty)
in _146_1480.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3033 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3033) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3036 -> begin
(let _146_1481 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1481 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3039 -> begin
([], ty)
end)
in (match (_57_3042) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3044 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3048 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1482 -> FStar_Syntax_Syntax.U_name (_146_1482))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3053, _57_3055, _57_3057, _57_3059, _57_3061, _57_3063, _57_3065) -> begin
(tc, uvs_universes)
end
| _57_3069 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3074 d -> (match (_57_3074) with
| (t, _57_3073) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3078, _57_3080, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _146_1486 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1486 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3090 -> begin
(FStar_All.failwith "Impossible")
end)
end)) data_types datas)))
end)
in (tcs, datas)))
end))
end))
end)))
end))))))))
in (

let _57_3100 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3094) -> begin
true
end
| _57_3097 -> begin
false
end))))
in (match (_57_3100) with
| (tys, datas) -> begin
(

let env0 = env
in (

let _57_3117 = (FStar_List.fold_right (fun tc _57_3106 -> (match (_57_3106) with
| (env, all_tcs, g) -> begin
(

let _57_3110 = (tc_tycon env tc)
in (match (_57_3110) with
| (env, tc, tc_u) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3112 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1490 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1490))
end else begin
()
end
in (let _146_1491 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1491))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3117) with
| (env, tcs, g) -> begin
(

let _57_3127 = (FStar_List.fold_right (fun se _57_3121 -> (match (_57_3121) with
| (datas, g) -> begin
(

let _57_3124 = (tc_data env tcs se)
in (match (_57_3124) with
| (data, g') -> begin
(let _146_1494 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1494))
end))
end)) datas ([], g))
in (match (_57_3127) with
| (datas, g) -> begin
(

let _57_3130 = (let _146_1495 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1495 datas))
in (match (_57_3130) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _146_1497 = (let _146_1496 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1496))
in FStar_Syntax_Syntax.Sig_bundle (_146_1497))
in (

let split_arrow = (fun t -> (match ((let _146_1500 = (FStar_Syntax_Subst.compress t)
in _146_1500.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _57_3139 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3143, _57_3145, t, _57_3148, _57_3150, _57_3152, _57_3154, _57_3156) -> begin
t
end
| _57_3160 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3164, us, _57_3167, _57_3169, _57_3171, _57_3173, _57_3175, _57_3177) -> begin
us
end
| _57_3181 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let _57_3185 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_57_3185) with
| (usubst, us) -> begin
(

let haseq_ty = (fun acc ty -> (

let _57_3209 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3191, bs, t, _57_3195, d_lids, _57_3198, _57_3200) -> begin
(lid, bs, t, d_lids)
end
| _57_3204 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_57_3209) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _146_1507 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _146_1507 t))
in (

let _57_3214 = (FStar_Syntax_Subst.open_term bs t)
in (match (_57_3214) with
| (bs, t) -> begin
(

let ibs = (match ((let _146_1508 = (FStar_Syntax_Subst.compress t)
in _146_1508.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _57_3217) -> begin
ibs
end
| _57_3221 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _146_1511 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1510 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_1511 _146_1510)))
in (

let ind = (let _146_1514 = (FStar_List.map (fun _57_3228 -> (match (_57_3228) with
| (bv, aq) -> begin
(let _146_1513 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_146_1513, aq))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _146_1514 None dr))
in (

let ind = (let _146_1517 = (FStar_List.map (fun _57_3232 -> (match (_57_3232) with
| (bv, aq) -> begin
(let _146_1516 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_146_1516, aq))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _146_1517 None dr))
in (

let haseq_ind = (let _146_1519 = (let _146_1518 = (FStar_Syntax_Syntax.as_arg ind)
in (_146_1518)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _146_1519 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _57_3243 = acc
in (match (_57_3243) with
| (_57_3237, en, _57_3240, _57_3242) -> begin
(

let opt = (let _146_1522 = (let _146_1521 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1521))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _146_1522 false))
in (match (opt) with
| None -> begin
false
end
| Some (_57_3247) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _146_1528 = (let _146_1527 = (let _146_1526 = (let _146_1525 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _146_1525))
in (_146_1526)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _146_1527 None dr))
in (FStar_Syntax_Util.mk_conj t _146_1528))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _57_3254 = fml
in (let _146_1534 = (let _146_1533 = (let _146_1532 = (let _146_1531 = (let _146_1530 = (let _146_1529 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_146_1529)::[])
in (_146_1530)::[])
in FStar_Syntax_Syntax.Meta_pattern (_146_1531))
in (fml, _146_1532))
in FStar_Syntax_Syntax.Tm_meta (_146_1533))
in {FStar_Syntax_Syntax.n = _146_1534; FStar_Syntax_Syntax.tk = _57_3254.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_3254.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_3254.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _146_1540 = (let _146_1539 = (let _146_1538 = (let _146_1537 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _146_1537 None))
in (FStar_Syntax_Syntax.as_arg _146_1538))
in (_146_1539)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _146_1540 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _146_1546 = (let _146_1545 = (let _146_1544 = (let _146_1543 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _146_1543 None))
in (FStar_Syntax_Syntax.as_arg _146_1544))
in (_146_1545)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _146_1546 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _57_3268 = acc
in (match (_57_3268) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3273, _57_3275, _57_3277, t_lid, _57_3280, _57_3282, _57_3284, _57_3286) -> begin
(t_lid = lid)
end
| _57_3290 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _146_1552 = (FStar_Syntax_Subst.compress dt)
in _146_1552.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _57_3299) -> begin
(

let dbs = (let _146_1553 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _146_1553))
in (

let dbs = (let _146_1554 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _146_1554 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _146_1559 = (let _146_1558 = (let _146_1557 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_146_1557)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _146_1558 None dr))
in (FStar_Syntax_Util.mk_conj t _146_1559))) FStar_Syntax_Util.t_true dbs)
in (

let _57_3310 = acc
in (match (_57_3310) with
| (env, cond') -> begin
(let _146_1561 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _146_1560 = (FStar_Syntax_Util.mk_conj cond' cond)
in (_146_1561, _146_1560)))
end))))))
end
| _57_3312 -> begin
acc
end))))
in (

let _57_3315 = (FStar_List.fold_left haseq_data (env, FStar_Syntax_Util.t_true) t_datas)
in (match (_57_3315) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _146_1563 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _146_1562 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((FStar_List.append l_axioms (((axiom_lid, fml))::[])), env, _146_1563, _146_1562))))
end))))))
end)))))))))))))))
end))))
end)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let debug_lid = (match ((FStar_List.hd tcs)) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3321, _57_3323, _57_3325, _57_3327, _57_3329, _57_3331, _57_3333) -> begin
lid
end
| _57_3337 -> begin
(FStar_All.failwith "Impossible!")
end)
in (

let _57_3339 = if is_noeq then begin
(FStar_Util.print1 "Skipping this type since noeq:%s\n" debug_lid.FStar_Ident.str)
end else begin
()
end
in if ((not ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid))) && (not (is_noeq))) then begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _57_3342 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _57_3344 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _57_3351 = (FStar_List.fold_left haseq_ty ([], env, FStar_Syntax_Util.t_true, FStar_Syntax_Util.t_true) tcs)
in (match (_57_3351) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _57_3353 = (FStar_Util.print1 "Checking tc_trivial_guard for:\n\n%s\n\n" debug_lid.FStar_Ident.str)
in (

let _57_3358 = (tc_trivial_guard env phi)
in (match (_57_3358) with
| (phi, _57_3357) -> begin
(

let _57_3359 = (let _146_1565 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 "Checking haseq soundness for:%s\n" _146_1565))
in (

let _57_3361 = (let _146_1566 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1566))
in (

let _57_3363 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _57_3369 -> (match (_57_3369) with
| (lid, fml) -> begin
(

let _57_3370 = (let _146_1569 = (FStar_Syntax_Print.term_to_string fml)
in (FStar_Util.print1 "Checking tc_assume for axiom:%s\n" _146_1569))
in (

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[]))))
end)) [] axioms)
in (let _146_1571 = (let _146_1570 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append (FStar_List.append tcs datas) ses), quals, lids, _146_1570))
in FStar_Syntax_Syntax.Sig_bundle (_146_1571)))))))
end))))
end))))))
end else begin
sig_bndle
end))))
end)))))))
end))
end))
end)))
end)))))))))


let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _146_1576 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1576))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
in (let _146_1577 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1577))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.GoOn -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Failed to process pragma: " s), r))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _57_3411 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3415 = (let _146_1582 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _146_1582 Prims.ignore))
in (

let _57_3420 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3422 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let ne = (tc_eff_decl env ne ForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne NotForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let _57_3444 = (let _146_1583 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1583))
in (match (_57_3444) with
| (a, wp_a_src) -> begin
(

let _57_3447 = (let _146_1584 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1584))
in (match (_57_3447) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _146_1588 = (let _146_1587 = (let _146_1586 = (let _146_1585 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _146_1585))
in FStar_Syntax_Syntax.NT (_146_1586))
in (_146_1587)::[])
in (FStar_Syntax_Subst.subst _146_1588 wp_b_tgt))
in (

let expected_k = (let _146_1593 = (let _146_1591 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1590 = (let _146_1589 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1589)::[])
in (_146_1591)::_146_1590))
in (let _146_1592 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1593 _146_1592)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _57_3451 = sub
in {FStar_Syntax_Syntax.source = _57_3451.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3451.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _57_3464 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3470 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3470) with
| (tps, c) -> begin
(

let _57_3474 = (tc_tparams env tps)
in (match (_57_3474) with
| (tps, env, us) -> begin
(

let _57_3478 = (tc_comp env c)
in (match (_57_3478) with
| (c, u, g) -> begin
(

let _57_3479 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3485 = (let _146_1594 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1594))
in (match (_57_3485) with
| (uvs, t) -> begin
(

let _57_3504 = (match ((let _146_1596 = (let _146_1595 = (FStar_Syntax_Subst.compress t)
in _146_1595.FStar_Syntax_Syntax.n)
in (tps, _146_1596))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3488, c)) -> begin
([], c)
end
| (_57_3494, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3501 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3504) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (se, env)))
end))
end)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3515 = ()
in (

let _57_3519 = (let _146_1598 = (let _146_1597 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1597))
in (check_and_gen env t _146_1598))
in (match (_57_3519) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _57_3539 = (tc_term env e)
in (match (_57_3539) with
| (e, c, g1) -> begin
(

let _57_3544 = (let _146_1602 = (let _146_1599 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1599))
in (let _146_1601 = (let _146_1600 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1600))
in (check_expected_effect env _146_1602 _146_1601)))
in (match (_57_3544) with
| (e, _57_3542, g) -> begin
(

let _57_3545 = (let _146_1603 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1603))
in (

let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1615 = (let _146_1614 = (let _146_1613 = (let _146_1612 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1611 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1610 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1612 _146_1611 _146_1610))))
in (_146_1613, r))
in FStar_Syntax_Syntax.Error (_146_1614))
in (Prims.raise _146_1615))
end
end))
in (

let _57_3589 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3566 lb -> (match (_57_3566) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3585 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3580 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3579 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1618 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1618, quals_opt))))
end)
in (match (_57_3585) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3589) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3598 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _146_1622 = (let _146_1621 = (let _146_1620 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1620))
in FStar_Syntax_Syntax.Tm_let (_146_1621))
in (FStar_Syntax_Syntax.mk _146_1622 None r))
in (

let _57_3632 = (match ((tc_maybe_toplevel_term (

let _57_3602 = env
in {FStar_TypeChecker_Env.solver = _57_3602.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3602.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3602.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3602.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3602.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3602.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3602.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3602.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3602.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3602.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3602.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3602.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3602.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3602.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3602.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3602.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3602.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3602.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3602.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3609; FStar_Syntax_Syntax.pos = _57_3607; FStar_Syntax_Syntax.vars = _57_3605}, _57_3616, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3620, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3626 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3629 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3632) with
| (se, lbs) -> begin
(

let _57_3638 = if (log env) then begin
(let _146_1630 = (let _146_1629 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _146_1626 = (let _146_1625 = (let _146_1624 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1624.FStar_Syntax_Syntax.fv_name)
in _146_1625.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1626))) with
| None -> begin
true
end
| _57_3636 -> begin
false
end)
in if should_log then begin
(let _146_1628 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1627 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1628 _146_1627)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1629 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1630))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3648 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3658 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3660) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3671, _57_3673) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3679 -> (match (_57_3679) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3685, _57_3687, quals, r) -> begin
(

let dec = (let _146_1646 = (let _146_1645 = (let _146_1644 = (let _146_1643 = (let _146_1642 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1642))
in FStar_Syntax_Syntax.Tm_arrow (_146_1643))
in (FStar_Syntax_Syntax.mk _146_1644 None r))
in (l, us, _146_1645, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1646))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3697, _57_3699, _57_3701, _57_3703, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3709 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3711, _57_3713, quals, _57_3716) -> begin
if (is_abstract quals) then begin
([], hidden)
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
((FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r)))::[], (l)::hidden)
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_13 -> (match (_57_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _57_3735 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3737) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3756, _57_3758, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1653 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1652 = (let _146_1651 = (let _146_1650 = (let _146_1649 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1649.FStar_Syntax_Syntax.fv_name)
in _146_1650.FStar_Syntax_Syntax.v)
in (_146_1651, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1652)))))
in (_146_1653, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3797 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3778 se -> (match (_57_3778) with
| (ses, exports, env, hidden) -> begin
(

let _57_3780 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1660 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1660))
end else begin
()
end
in (

let _57_3784 = (tc_decl env se)
in (match (_57_3784) with
| (se, env) -> begin
(

let _57_3785 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1661 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1661))
end else begin
()
end
in (

let _57_3787 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3791 = (for_export hidden se)
in (match (_57_3791) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3797) with
| (ses, exports, env, _57_3796) -> begin
(let _146_1662 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1662, env))
end)))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let _57_3802 = env
in (let _146_1667 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3802.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3802.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3802.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3802.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3802.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3802.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3802.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3802.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3802.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3802.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3802.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3802.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3802.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3802.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3802.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3802.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1667; FStar_TypeChecker_Env.type_of = _57_3802.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3802.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3802.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3805 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _57_3811 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3811) with
| (ses, exports, env) -> begin
((

let _57_3812 = modul
in {FStar_Syntax_Syntax.name = _57_3812.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3812.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3812.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _57_3820 = (tc_decls env decls)
in (match (_57_3820) with
| (ses, exports, env) -> begin
(

let modul = (

let _57_3821 = modul
in {FStar_Syntax_Syntax.name = _57_3821.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3821.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3821.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _57_3827 = modul
in {FStar_Syntax_Syntax.name = _57_3827.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3827.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _57_3837 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3831 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3833 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3835 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1680 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _146_1680 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _57_3844 = (tc_partial_modul env modul)
in (match (_57_3844) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_3847 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1689 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1689))
end else begin
()
end
in (

let env = (

let _57_3849 = env
in {FStar_TypeChecker_Env.solver = _57_3849.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3849.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3849.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3849.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3849.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3849.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3849.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3849.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3849.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3849.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3849.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3849.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3849.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3849.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3849.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3849.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3849.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3849.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3849.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3849.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3865 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3857) -> begin
(let _146_1694 = (let _146_1693 = (let _146_1692 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1692))
in FStar_Syntax_Syntax.Error (_146_1693))
in (Prims.raise _146_1694))
end
in (match (_57_3865) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1699 = (let _146_1698 = (let _146_1697 = (let _146_1695 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1695))
in (let _146_1696 = (FStar_TypeChecker_Env.get_range env)
in (_146_1697, _146_1696)))
in FStar_Syntax_Syntax.Error (_146_1698))
in (Prims.raise _146_1699))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3868 = if (FStar_Options.debug_any ()) then begin
(let _146_1704 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1704))
end else begin
()
end
in (

let _57_3872 = (tc_modul env m)
in (match (_57_3872) with
| (m, env) -> begin
(

let _57_3873 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1705 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1705))
end else begin
()
end
in (m, env))
end))))




