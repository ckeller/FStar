open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___93_5 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___93_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___93_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___93_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___93_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___93_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___93_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___93_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___93_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___93_5.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___93_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___93_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___93_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___93_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___93_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___93_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___93_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___93_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___93_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___93_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___93_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___93_5.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.type_of =
        (uu___93_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___93_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___93_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___93_5.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___93_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___93_5.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___93_5.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___93_5.FStar_TypeChecker_Env.identifier_info)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___94_10 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___94_10.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___94_10.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___94_10.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___94_10.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___94_10.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___94_10.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___94_10.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___94_10.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___94_10.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___94_10.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___94_10.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___94_10.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___94_10.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___94_10.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___94_10.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___94_10.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___94_10.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___94_10.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___94_10.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___94_10.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___94_10.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.type_of =
        (uu___94_10.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___94_10.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___94_10.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___94_10.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___94_10.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___94_10.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___94_10.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___94_10.FStar_TypeChecker_Env.identifier_info)
    }
let mk_lex_list:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun vs  ->
    FStar_List.fold_right
      (fun v1  ->
         fun tl1  ->
           let r =
             if tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v1.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos
                 tl1.FStar_Syntax_Syntax.pos in
           let uu____43 =
             let uu____44 =
               let uu____45 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____46 =
                 let uu____49 = FStar_Syntax_Syntax.as_arg tl1 in [uu____49] in
               uu____45 :: uu____46 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____44 in
           uu____43 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
let is_eq:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___88_57  ->
    match uu___88_57 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____60 -> false
let steps:
  'Auu____67 . 'Auu____67 -> FStar_TypeChecker_Normalize.step Prims.list =
  fun env  ->
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.Eager_unfolding]
let norm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
let norm_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
let check_no_escape:
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> t
            | uu____121 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____129 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____129 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____139 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____141 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____141
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____143 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____144 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____143 uu____144 in
                          let uu____145 =
                            let uu____146 =
                              let uu____151 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____151) in
                            FStar_Errors.Error uu____146 in
                          FStar_Exn.raise uu____145 in
                        let s =
                          let uu____153 =
                            let uu____154 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____154 in
                          FStar_TypeChecker_Util.new_uvar env uu____153 in
                        let uu____163 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____163 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____168 -> fail ())) in
          aux false kt
let push_binding:
  'Auu____177 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____177) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let maybe_extend_subst:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____210 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____210
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___95_226 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___95_226.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___95_226.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____229  ->
             let uu____230 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____230 t)
      }
let memo_tk:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> e
let value_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          let should_return t =
            let uu____281 =
              let uu____282 = FStar_Syntax_Subst.compress t in
              uu____282.FStar_Syntax_Syntax.n in
            match uu____281 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____285,c) ->
                let uu____303 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____303
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____305 =
                    let uu____306 = FStar_Syntax_Subst.compress t1 in
                    uu____306.FStar_Syntax_Syntax.n in
                  (match uu____305 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____310 -> false
                   | uu____311 -> true)
                else false
            | uu____313 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____316 =
                  let uu____319 =
                    (let uu____322 = should_return t in
                     Prims.op_Negation uu____322) ||
                      (let uu____324 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____324) in
                  if uu____319
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____316
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____332 =
            let uu____339 = FStar_TypeChecker_Env.expected_typ env in
            match uu____339 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____350 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____350
                  then
                    let uu____351 = FStar_Syntax_Print.term_to_string t in
                    let uu____352 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____351
                      uu____352
                  else ());
                 (let uu____354 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____354 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____370 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____370 with
                       | (e2,g) ->
                           ((let uu____384 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____384
                             then
                               let uu____385 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____386 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____387 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____388 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____385 uu____386 uu____387 uu____388
                             else ());
                            (let msg =
                               let uu____395 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____395
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_41  ->
                                      FStar_Pervasives_Native.Some _0_41)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____412 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____412 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2)))))) in
          match uu____332 with
          | (e1,lc1,g) ->
              ((let uu____435 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____435
                then
                  let uu____436 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____436
                else ());
               (e1, lc1, g))
let comp_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____462 = FStar_TypeChecker_Env.expected_typ env in
        match uu____462 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____472 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____472 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
let check_expected_effect:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun copt  ->
      fun uu____508  ->
        match uu____508 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____537 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____537
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____539 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____539
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____541 =
              match copt with
              | FStar_Pervasives_Native.Some uu____554 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____557 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____559 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____559)) in
                  if uu____557
                  then
                    let uu____566 =
                      let uu____569 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____569 in
                    (uu____566, c)
                  else
                    (let uu____573 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____573
                     then
                       let uu____580 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____580)
                     else
                       (let uu____584 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____584
                        then
                          let uu____591 =
                            let uu____594 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____594 in
                          (uu____591, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____541 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____620 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____620 with
                       | (e1,uu____634,g) ->
                           let g1 =
                             let uu____637 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____637
                               "could not prove post-condition" g in
                           ((let uu____639 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____639
                             then
                               let uu____640 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____641 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____640 uu____641
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard:
  'Auu____652 'Auu____653 .
    FStar_TypeChecker_Env.env ->
      ('Auu____653,'Auu____652,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____653,'Auu____652,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____673  ->
      match uu____673 with
      | (te,kt,f) ->
          let uu____683 = FStar_TypeChecker_Rel.guard_form f in
          (match uu____683 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____691 =
                 let uu____692 =
                   let uu____697 =
                     FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                       env f1 in
                   let uu____698 = FStar_TypeChecker_Env.get_range env in
                   (uu____697, uu____698) in
                 FStar_Errors.Error uu____692 in
               FStar_Exn.raise uu____691)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____709 = FStar_TypeChecker_Env.expected_typ env in
    match uu____709 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None"
    | FStar_Pervasives_Native.Some t ->
        let uu____713 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____713
let rec get_pat_vars:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats in
      let uu____737 = FStar_Syntax_Util.head_and_args pats1 in
      match uu____737 with
      | (head1,args) ->
          let uu____776 =
            let uu____777 = FStar_Syntax_Util.un_uinst head1 in
            uu____777.FStar_Syntax_Syntax.n in
          (match uu____776 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____784 = FStar_List.tl args in
               get_pat_vars_args uu____784 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____793 ->
               let uu____794 = FStar_Syntax_Free.names pats1 in
               FStar_Util.set_union acc uu____794)
and get_pat_vars_args:
  FStar_Syntax_Syntax.args ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun args  ->
    fun acc  ->
      FStar_List.fold_left
        (fun s  ->
           fun arg  -> get_pat_vars (FStar_Pervasives_Native.fst arg) s) acc
        args
let check_smt_pat:
  'Auu____829 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____829) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____862 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____862
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____863;
                  FStar_Syntax_Syntax.effect_name = uu____864;
                  FStar_Syntax_Syntax.result_typ = uu____865;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____869)::[];
                  FStar_Syntax_Syntax.flags = uu____870;_}
                ->
                let pat_vars =
                  let uu____918 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats in
                  let uu____919 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv in
                  get_pat_vars uu____918 uu____919 in
                let uu____922 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____949  ->
                          match uu____949 with
                          | (b,uu____955) ->
                              let uu____956 = FStar_Util.set_mem b pat_vars in
                              Prims.op_Negation uu____956)) in
                (match uu____922 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____962) ->
                     let uu____967 =
                       let uu____968 = FStar_Syntax_Print.bv_to_string x in
                       FStar_Util.format1
                         "Pattern misses at least one bound variable: %s"
                         uu____968 in
                     FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____967)
            | uu____969 -> failwith "Impossible"
          else ()
let guard_letrecs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____999 =
          let uu____1000 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____1000 in
        if uu____999
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___96_1031 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___96_1031.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___96_1031.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___96_1031.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___96_1031.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___96_1031.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___96_1031.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___96_1031.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___96_1031.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___96_1031.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___96_1031.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___96_1031.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___96_1031.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___96_1031.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___96_1031.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___96_1031.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___96_1031.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___96_1031.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___96_1031.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___96_1031.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___96_1031.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___96_1031.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.type_of =
                     (uu___96_1031.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___96_1031.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___96_1031.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___96_1031.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___96_1031.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___96_1031.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___96_1031.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___96_1031.FStar_TypeChecker_Env.identifier_info)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Parser_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____1065  ->
                           match uu____1065 with
                           | (b,uu____1073) ->
                               let t =
                                 let uu____1075 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____1075 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____1078 ->
                                    []
                                | FStar_Syntax_Syntax.Tm_arrow uu____1079 ->
                                    []
                                | uu____1092 ->
                                    let uu____1093 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____1093]))) in
                 let as_lex_list dec =
                   let uu____1098 = FStar_Syntax_Util.head_and_args dec in
                   match uu____1098 with
                   | (head1,uu____1114) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.lexcons_lid
                            -> dec
                        | uu____1136 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____1140 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___89_1149  ->
                           match uu___89_1149 with
                           | FStar_Syntax_Syntax.DECREASES uu____1150 -> true
                           | uu____1153 -> false)) in
                 match uu____1140 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.DECREASES dec) -> as_lex_list dec
                 | uu____1157 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____1166 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____1183 =
                 match uu____1183 with
                 | (l,t) ->
                     let uu____1196 =
                       let uu____1197 = FStar_Syntax_Subst.compress t in
                       uu____1197.FStar_Syntax_Syntax.n in
                     (match uu____1196 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____1256  ->
                                    match uu____1256 with
                                    | (x,imp) ->
                                        let uu____1267 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____1267
                                        then
                                          let uu____1272 =
                                            let uu____1273 =
                                              let uu____1276 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              FStar_Pervasives_Native.Some
                                                uu____1276 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____1273
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____1272, imp)
                                        else (x, imp))) in
                          let uu____1278 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____1278 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____1295 =
                                   let uu____1296 =
                                     let uu____1297 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____1298 =
                                       let uu____1301 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____1301] in
                                     uu____1297 :: uu____1298 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____1296 in
                                 uu____1295 FStar_Pervasives_Native.None r in
                               let uu____1304 = FStar_Util.prefix formals2 in
                               (match uu____1304 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___97_1349 = last1 in
                                      let uu____1350 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___97_1349.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___97_1349.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____1350
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____1376 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____1376
                                      then
                                        let uu____1377 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____1378 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____1379 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____1377 uu____1378 uu____1379
                                      else ());
                                     (l, t'))))
                      | uu____1383 ->
                          FStar_Exn.raise
                            (FStar_Errors.Error
                               ("Annotated type of 'let rec' must be an arrow",
                                 (t.FStar_Syntax_Syntax.pos)))) in
               FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))
let rec tc_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___98_1814 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___98_1814.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___98_1814.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___98_1814.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___98_1814.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___98_1814.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___98_1814.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___98_1814.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___98_1814.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___98_1814.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___98_1814.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___98_1814.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___98_1814.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___98_1814.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___98_1814.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___98_1814.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___98_1814.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___98_1814.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___98_1814.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___98_1814.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___98_1814.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___98_1814.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.type_of =
             (uu___98_1814.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___98_1814.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___98_1814.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___98_1814.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___98_1814.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___98_1814.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___98_1814.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___98_1814.FStar_TypeChecker_Env.identifier_info)
         }) e
and tc_maybe_toplevel_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      (let uu____1826 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1826
       then
         let uu____1827 =
           let uu____1828 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1828 in
         let uu____1829 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1827 uu____1829
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1838 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1869 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1876 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1893 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1894 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1895 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1896 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1897 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1914 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1927 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1934 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1940 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1940 with
            | (e2,c,g) ->
                let g1 =
                  let uu___99_1957 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___99_1957.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___99_1957.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___99_1957.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1974 = FStar_Syntax_Util.type_u () in
           (match uu____1974 with
            | (t,u) ->
                let uu____1987 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1987 with
                 | (e2,c,g) ->
                     let uu____2003 =
                       let uu____2018 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____2018 with
                       | (env2,uu____2040) -> tc_pats env2 pats in
                     (match uu____2003 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___100_2074 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___100_2074.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___100_2074.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___100_2074.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2075 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2078 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2075, c, uu____2078))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2086 =
             let uu____2087 = FStar_Syntax_Subst.compress e1 in
             uu____2087.FStar_Syntax_Syntax.n in
           (match uu____2086 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2096,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2098;
                               FStar_Syntax_Syntax.lbtyp = uu____2099;
                               FStar_Syntax_Syntax.lbeff = uu____2100;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2125 =
                  let uu____2132 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2132 e11 in
                (match uu____2125 with
                 | (e12,c1,g1) ->
                     let uu____2142 = tc_term env1 e2 in
                     (match uu____2142 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1
                              (FStar_Pervasives_Native.None, c2) in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ in
                          let e3 =
                            let uu____2166 =
                              let uu____2169 =
                                let uu____2170 =
                                  let uu____2183 =
                                    let uu____2190 =
                                      let uu____2193 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2193] in
                                    (false, uu____2190) in
                                  (uu____2183, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2170 in
                              FStar_Syntax_Syntax.mk uu____2169 in
                            uu____2166 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2215 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2215)))
            | uu____2218 ->
                let uu____2219 = tc_term env1 e1 in
                (match uu____2219 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2241) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2258 = tc_term env1 e1 in
           (match uu____2258 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2282) ->
           let uu____2329 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2329 with
            | (env0,uu____2343) ->
                let uu____2348 = tc_comp env0 expected_c in
                (match uu____2348 with
                 | (expected_c1,uu____2362,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2367 =
                       let uu____2374 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2374 e1 in
                     (match uu____2367 with
                      | (e2,c',g') ->
                          let uu____2384 =
                            let uu____2391 =
                              let uu____2396 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2396) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2391 in
                          (match uu____2384 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inl t_res),
                                          FStar_Pervasives_Native.None),
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____2451 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2451 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2460 =
                                            FStar_Syntax_Util.mk_squash f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2460) in
                               let uu____2461 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2461 with
                                | (e5,c,f2) ->
                                    let uu____2477 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____2477))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2481) ->
           let uu____2528 = FStar_Syntax_Util.type_u () in
           (match uu____2528 with
            | (k,u) ->
                let uu____2541 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2541 with
                 | (t1,uu____2555,f) ->
                     let uu____2557 =
                       let uu____2564 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2564 e1 in
                     (match uu____2557 with
                      | (e2,c,g) ->
                          let uu____2574 =
                            let uu____2579 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2583  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2579 e2 c f in
                          (match uu____2574 with
                           | (c1,f1) ->
                               let uu____2592 =
                                 let uu____2599 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2599 c1 in
                               (match uu____2592 with
                                | (e3,c2,f2) ->
                                    let uu____2639 =
                                      let uu____2640 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2640 in
                                    (e3, c2, uu____2639))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2641;
              FStar_Syntax_Syntax.vars = uu____2642;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2705 = FStar_Syntax_Util.head_and_args top in
           (match uu____2705 with
            | (unary_op,uu____2727) ->
                let head1 =
                  let uu____2751 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2751 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2789);
              FStar_Syntax_Syntax.pos = uu____2790;
              FStar_Syntax_Syntax.vars = uu____2791;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2854 = FStar_Syntax_Util.head_and_args top in
           (match uu____2854 with
            | (unary_op,uu____2876) ->
                let head1 =
                  let uu____2900 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2900 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2938;
              FStar_Syntax_Syntax.vars = uu____2939;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2972 =
               let uu____2979 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2979 with | (env0,uu____2993) -> tc_term env0 e1 in
             match uu____2972 with
             | (e2,c,g) ->
                 let uu____3007 = FStar_Syntax_Util.head_and_args top in
                 (match uu____3007 with
                  | (reify_op,uu____3029) ->
                      let u_c =
                        let uu____3051 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____3051 with
                        | (uu____3058,c',uu____3060) ->
                            let uu____3061 =
                              let uu____3062 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____3062.FStar_Syntax_Syntax.n in
                            (match uu____3061 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____3066 ->
                                 let uu____3067 = FStar_Syntax_Util.type_u () in
                                 (match uu____3067 with
                                  | (t,u) ->
                                      let g_opt =
                                        FStar_TypeChecker_Rel.try_teq true
                                          env1 c'.FStar_Syntax_Syntax.res_typ
                                          t in
                                      ((match g_opt with
                                        | FStar_Pervasives_Native.Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env1 g'
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____3079 =
                                              let uu____3080 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____3081 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____3082 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____3080 uu____3081
                                                uu____3082 in
                                            failwith uu____3079);
                                       u))) in
                      let repr =
                        let uu____3084 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____3084 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          FStar_Pervasives_Native.None
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____3105 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____3105
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____3106 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____3106 with
                       | (e4,c2,g') ->
                           let uu____3122 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____3122)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3124;
              FStar_Syntax_Syntax.vars = uu____3125;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3167 =
               let uu____3168 =
                 let uu____3169 =
                   let uu____3174 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____3174, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____3169 in
               FStar_Exn.raise uu____3168 in
             let uu____3181 = FStar_Syntax_Util.head_and_args top in
             match uu____3181 with
             | (reflect_op,uu____3203) ->
                 let uu____3224 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3224 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3257 =
                        let uu____3258 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3258 in
                      if uu____3257
                      then no_reflect ()
                      else
                        (let uu____3268 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3268 with
                         | (env_no_ex,topt) ->
                             let uu____3287 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____3307 =
                                   let uu____3310 =
                                     let uu____3311 =
                                       let uu____3326 =
                                         let uu____3329 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____3330 =
                                           let uu____3333 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____3333] in
                                         uu____3329 :: uu____3330 in
                                       (repr, uu____3326) in
                                     FStar_Syntax_Syntax.Tm_app uu____3311 in
                                   FStar_Syntax_Syntax.mk uu____3310 in
                                 uu____3307 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____3339 =
                                 let uu____3346 =
                                   let uu____3347 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____3347
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____3346 t in
                               match uu____3339 with
                               | (t1,uu____3375,g) ->
                                   let uu____3377 =
                                     let uu____3378 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____3378.FStar_Syntax_Syntax.n in
                                   (match uu____3377 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____3393,(res,uu____3395)::
                                         (wp,uu____3397)::[])
                                        -> (t1, res, wp, g)
                                    | uu____3440 -> failwith "Impossible") in
                             (match uu____3287 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____3471 =
                                    let uu____3476 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____3476 with
                                    | (e2,c,g) ->
                                        ((let uu____3491 =
                                            let uu____3492 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____3492 in
                                          if uu____3491
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____3502 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____3502 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____3510 =
                                                  let uu____3517 =
                                                    let uu____3522 =
                                                      let uu____3523 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____3524 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____3523 uu____3524 in
                                                    (uu____3522,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____3517] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____3510);
                                               (let uu____3533 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____3533)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____3535 =
                                                let uu____3536 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____3536 in
                                              (e2, uu____3535))) in
                                  (match uu____3471 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____3546 =
                                           let uu____3547 =
                                             let uu____3548 =
                                               let uu____3549 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____3549] in
                                             let uu____3550 =
                                               let uu____3559 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____3559] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____3548;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____3550;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3547 in
                                         FStar_All.pipe_right uu____3546
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____3579 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____3579 with
                                        | (e4,c1,g') ->
                                            let uu____3595 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____3595))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____3642 =
               let uu____3643 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____3643 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____3642 instantiate_both in
           ((let uu____3659 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____3659
             then
               let uu____3660 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____3661 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____3660
                 uu____3661
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.quote_lid
                   -> true
               | uu____3665 -> false in
             let uu____3666 = tc_term (no_inst env2) head1 in
             match uu____3666 with
             | (head2,chead,g_head) ->
                 let uu____3682 =
                   let uu____3689 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____3689
                   then
                     let uu____3696 =
                       let uu____3703 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____3703 in
                     match uu____3696 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____3716 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____3718 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____3718))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____3716
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____3723 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____3723) in
                 (match uu____3682 with
                  | (e1,c,g) ->
                      ((let uu____3736 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____3736
                        then
                          let uu____3737 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____3737
                        else ());
                       (let uu____3739 = comp_check_expected_typ env0 e1 c in
                        match uu____3739 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____3756 =
                                let uu____3757 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____3757.FStar_Syntax_Syntax.n in
                              match uu____3756 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____3761) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___101_3823 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___101_3823.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___101_3823.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___101_3823.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____3872 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____3874 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____3874 in
                            ((let uu____3876 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____3876
                              then
                                let uu____3877 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____3878 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____3877 uu____3878
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____3918 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____3918 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____3938 = tc_term env12 e1 in
                (match uu____3938 with
                 | (e11,c1,g1) ->
                     let uu____3954 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____3964 = FStar_Syntax_Util.type_u () in
                           (match uu____3964 with
                            | (k,uu____3974) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____3976 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____3976, res_t)) in
                     (match uu____3954 with
                      | (env_branches,res_t) ->
                          ((let uu____3986 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____3986
                            then
                              let uu____3987 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____3987
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4073 =
                              let uu____4078 =
                                FStar_List.fold_right
                                  (fun uu____4124  ->
                                     fun uu____4125  ->
                                       match (uu____4124, uu____4125) with
                                       | ((uu____4188,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4248 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____4248))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4078 with
                              | (cases,g) ->
                                  let uu____4287 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____4287, g) in
                            match uu____4073 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (FStar_Pervasives_Native.Some e11) c1
                                    ((FStar_Pervasives_Native.Some guard_x),
                                      c_branches) in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____4383  ->
                                              match uu____4383 with
                                              | ((pat,wopt,br),uu____4411,lc,uu____4413)
                                                  ->
                                                  let uu____4426 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____4426))) in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres.FStar_Syntax_Syntax.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos in
                                  let uu____4481 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____4481
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____4488 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____4488 in
                                     let lb =
                                       let uu____4492 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (FStar_Util.Inl guard_x);
                                         FStar_Syntax_Syntax.lbunivs = [];
                                         FStar_Syntax_Syntax.lbtyp =
                                           (c1.FStar_Syntax_Syntax.res_typ);
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____4492;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____4496 =
                                         let uu____4499 =
                                           let uu____4500 =
                                             let uu____4513 =
                                               let uu____4514 =
                                                 let uu____4515 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____4515] in
                                               FStar_Syntax_Subst.close
                                                 uu____4514 e_match in
                                             ((false, [lb]), uu____4513) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____4500 in
                                         FStar_Syntax_Syntax.mk uu____4499 in
                                       uu____4496
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____4528 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____4528
                                  then
                                    let uu____4529 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____4530 =
                                      let uu____4531 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____4531 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____4529 uu____4530
                                  else ());
                                 (let uu____4533 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____4533))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____4536;
                FStar_Syntax_Syntax.lbunivs = uu____4537;
                FStar_Syntax_Syntax.lbtyp = uu____4538;
                FStar_Syntax_Syntax.lbeff = uu____4539;
                FStar_Syntax_Syntax.lbdef = uu____4540;_}::[]),uu____4541)
           ->
           ((let uu____4561 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____4561
             then
               let uu____4562 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____4562
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____4564),uu____4565) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____4580;
                FStar_Syntax_Syntax.lbunivs = uu____4581;
                FStar_Syntax_Syntax.lbtyp = uu____4582;
                FStar_Syntax_Syntax.lbeff = uu____4583;
                FStar_Syntax_Syntax.lbdef = uu____4584;_}::uu____4585),uu____4586)
           ->
           ((let uu____4608 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____4608
             then
               let uu____4609 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____4609
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____4611),uu____4612) ->
           check_inner_let_rec env1 top)
and tc_synth:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun args  ->
      fun rng  ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____4644 =
            let uu____4645 =
              let uu____4646 =
                FStar_TypeChecker_Util.fvar_const env
                  FStar_Parser_Const.magic_lid in
              let uu____4647 =
                let uu____4648 =
                  FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
                [uu____4648] in
              FStar_Syntax_Syntax.mk_Tm_app uu____4646 uu____4647 in
            uu____4645 FStar_Pervasives_Native.None rng in
          tc_term env uu____4644
        else
          (let uu____4652 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 (tau, FStar_Pervasives_Native.None, rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                uu____4742))::(tau,FStar_Pervasives_Native.None )::rest ->
                 (tau, (FStar_Pervasives_Native.Some a), rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                uu____4802))::(uu____4803,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____4804))::
                 (tau,FStar_Pervasives_Native.None )::rest ->
                 (tau, (FStar_Pervasives_Native.Some a), rest)
             | uu____4877 ->
                 FStar_Exn.raise
                   (FStar_Errors.Error
                      ("synth_by_tactic: bad application", rng)) in
           match uu____4652 with
           | (tau,atyp,rest) ->
               let typ =
                 match atyp with
                 | FStar_Pervasives_Native.Some t -> t
                 | FStar_Pervasives_Native.None  ->
                     let uu____4961 = FStar_TypeChecker_Env.expected_typ env in
                     (match uu____4961 with
                      | FStar_Pervasives_Native.Some t -> t
                      | FStar_Pervasives_Native.None  ->
                          let uu____4967 =
                            let uu____4968 =
                              let uu____4973 =
                                FStar_TypeChecker_Env.get_range env in
                              ("synth_by_tactic: need a type annotation when no expected type is present",
                                uu____4973) in
                            FStar_Errors.Error uu____4968 in
                          FStar_Exn.raise uu____4967) in
               let uu____4976 = FStar_TypeChecker_Env.clear_expected_typ env in
               (match uu____4976 with
                | (env',uu____4990) ->
                    let uu____4995 = tc_term env' typ in
                    (match uu____4995 with
                     | (typ1,uu____5009,g1) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                          (let uu____5012 = tc_tactic env' tau in
                           match uu____5012 with
                           | (tau1,uu____5026,g2) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env' g2;
                                (let uu____5030 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Tac") in
                                 if uu____5030
                                 then
                                   let uu____5031 =
                                     FStar_Syntax_Print.term_to_string tau1 in
                                   let uu____5032 =
                                     FStar_Syntax_Print.term_to_string typ1 in
                                   FStar_Util.print2
                                     "Running tactic %s at return type %s\n"
                                     uu____5031 uu____5032
                                 else ());
                                (let t =
                                   env.FStar_TypeChecker_Env.synth env' typ1
                                     tau1 in
                                 (let uu____5036 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Tac") in
                                  if uu____5036
                                  then
                                    let uu____5037 =
                                      FStar_Syntax_Print.term_to_string t in
                                    FStar_Util.print1 "Got %s\n" uu____5037
                                  else ());
                                 FStar_TypeChecker_Util.check_uvars
                                   tau1.FStar_Syntax_Syntax.pos t;
                                 (let uu____5040 =
                                    FStar_Syntax_Syntax.mk_Tm_app t rest
                                      FStar_Pervasives_Native.None rng in
                                  tc_term env uu____5040))))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___102_5044 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___102_5044.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___102_5044.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___102_5044.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___102_5044.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___102_5044.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___102_5044.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___102_5044.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___102_5044.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___102_5044.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___102_5044.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___102_5044.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___102_5044.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___102_5044.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___102_5044.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___102_5044.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___102_5044.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___102_5044.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___102_5044.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___102_5044.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___102_5044.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___102_5044.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.type_of =
            (uu___102_5044.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___102_5044.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___102_5044.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___102_5044.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___102_5044.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___102_5044.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___102_5044.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___102_5044.FStar_TypeChecker_Env.identifier_info)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit
and tc_reified_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___103_5048 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___103_5048.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___103_5048.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___103_5048.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___103_5048.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___103_5048.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___103_5048.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___103_5048.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___103_5048.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___103_5048.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___103_5048.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___103_5048.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___103_5048.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___103_5048.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___103_5048.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___103_5048.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___103_5048.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___103_5048.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___103_5048.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___103_5048.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___103_5048.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___103_5048.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.type_of =
            (uu___103_5048.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___103_5048.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___103_5048.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___103_5048.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___103_5048.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___103_5048.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___103_5048.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___103_5048.FStar_TypeChecker_Env.identifier_info)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit
and tc_tactic_opt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some tactic ->
          let uu____5064 = tc_tactic env tactic in
          (match uu____5064 with
           | (tactic1,uu____5074,uu____5075) ->
               FStar_Pervasives_Native.Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____5114 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____5114 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____5135 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____5135
              then FStar_Util.Inl t1
              else
                (let uu____5141 =
                   let uu____5142 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____5142 in
                 FStar_Util.Inr uu____5141) in
            let is_data_ctor uu___90_5152 =
              match uu___90_5152 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____5155) -> true
              | uu____5162 -> false in
            let uu____5165 =
              (is_data_ctor dc) &&
                (let uu____5167 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____5167) in
            if uu____5165
            then
              let uu____5174 =
                let uu____5175 =
                  let uu____5180 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____5181 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____5180, uu____5181) in
                FStar_Errors.Error uu____5175 in
              FStar_Exn.raise uu____5174
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____5198 =
            let uu____5199 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____5199 in
          failwith uu____5198
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____5233 =
              let uu____5234 = FStar_Syntax_Subst.compress t1 in
              uu____5234.FStar_Syntax_Syntax.n in
            match uu____5233 with
            | FStar_Syntax_Syntax.Tm_arrow uu____5237 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____5250 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___104_5288 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___104_5288.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___104_5288.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___104_5288.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____5340 =
            let uu____5353 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____5353 with
            | FStar_Pervasives_Native.None  ->
                let uu____5368 = FStar_Syntax_Util.type_u () in
                (match uu____5368 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____5340 with
           | (t,uu____5405,g0) ->
               let uu____5419 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____5419 with
                | (e1,uu____5439,g1) ->
                    let uu____5453 =
                      let uu____5454 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____5454
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____5455 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____5453, uu____5455)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____5457 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____5470 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____5470)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____5457 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___105_5489 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___105_5489.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___105_5489.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____5492 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____5492 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____5513 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____5513
                       then FStar_Util.Inl t1
                       else
                         (let uu____5519 =
                            let uu____5520 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____5520 in
                          FStar_Util.Inr uu____5519) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____5526;
             FStar_Syntax_Syntax.vars = uu____5527;_},uu____5528)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____5533 =
            let uu____5534 =
              let uu____5539 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____5539) in
            FStar_Errors.Error uu____5534 in
          FStar_Exn.raise uu____5533
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____5547 =
            let uu____5548 =
              let uu____5553 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____5553) in
            FStar_Errors.Error uu____5548 in
          FStar_Exn.raise uu____5547
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____5561;
             FStar_Syntax_Syntax.vars = uu____5562;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____5571 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5571 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____5594 =
                     let uu____5595 =
                       let uu____5600 =
                         let uu____5601 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____5602 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____5603 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____5601 uu____5602 uu____5603 in
                       let uu____5604 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____5600, uu____5604) in
                     FStar_Errors.Error uu____5595 in
                   FStar_Exn.raise uu____5594)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____5620 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____5624 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____5624 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5626 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5626 with
           | ((us,t),range) ->
               ((let uu____5649 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____5649
                 then
                   let uu____5650 =
                     let uu____5651 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____5651 in
                   let uu____5652 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____5653 = FStar_Range.string_of_range range in
                   let uu____5654 = FStar_Range.string_of_use_range range in
                   let uu____5655 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____5650 uu____5652 uu____5653 uu____5654 uu____5655
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____5660 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____5660 us in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____5684 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____5684 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____5698 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____5698 with
                | (env2,uu____5712) ->
                    let uu____5717 = tc_binders env2 bs1 in
                    (match uu____5717 with
                     | (bs2,env3,g,us) ->
                         let uu____5736 = tc_comp env3 c1 in
                         (match uu____5736 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___106_5755 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___106_5755.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___106_5755.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____5764 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____5764 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____5783 =
            let uu____5788 =
              let uu____5789 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5789] in
            FStar_Syntax_Subst.open_term uu____5788 phi in
          (match uu____5783 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____5799 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____5799 with
                | (env2,uu____5813) ->
                    let uu____5818 =
                      let uu____5831 = FStar_List.hd x1 in
                      tc_binder env2 uu____5831 in
                    (match uu____5818 with
                     | (x2,env3,f1,u) ->
                         ((let uu____5859 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____5859
                           then
                             let uu____5860 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____5861 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____5862 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____5860 uu____5861 uu____5862
                           else ());
                          (let uu____5864 = FStar_Syntax_Util.type_u () in
                           match uu____5864 with
                           | (t_phi,uu____5876) ->
                               let uu____5877 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____5877 with
                                | (phi2,uu____5891,f2) ->
                                    let e1 =
                                      let uu___107_5896 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___107_5896.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___107_5896.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____5903 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____5903 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5916) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____5939 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____5939
            then
              let uu____5940 =
                FStar_Syntax_Print.term_to_string
                  (let uu___108_5943 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___108_5943.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___108_5943.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____5940
            else ());
           (let uu____5949 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____5949 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____5962 ->
          let uu____5963 =
            let uu____5964 = FStar_Syntax_Print.term_to_string top in
            let uu____5965 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____5964
              uu____5965 in
          failwith uu____5963
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
      | FStar_Const.Const_bool uu____5974 -> FStar_Syntax_Util.t_bool
      | FStar_Const.Const_int (uu____5975,FStar_Pervasives_Native.None ) ->
          FStar_Syntax_Syntax.t_int
      | FStar_Const.Const_int
          (uu____5986,FStar_Pervasives_Native.Some uu____5987) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____6002 -> FStar_Syntax_Syntax.t_string
      | FStar_Const.Const_float uu____6007 -> FStar_Syntax_Syntax.t_float
      | FStar_Const.Const_char uu____6008 -> FStar_Syntax_Syntax.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____6009 -> FStar_Syntax_Syntax.t_range
      | uu____6010 ->
          FStar_Exn.raise (FStar_Errors.Error ("Unsupported constant", r))
and tc_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.universe,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun c  ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____6027) ->
          let uu____6036 = FStar_Syntax_Util.type_u () in
          (match uu____6036 with
           | (k,u) ->
               let uu____6049 = tc_check_tot_or_gtot_term env t k in
               (match uu____6049 with
                | (t1,uu____6063,g) ->
                    let uu____6065 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6065, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____6067) ->
          let uu____6076 = FStar_Syntax_Util.type_u () in
          (match uu____6076 with
           | (k,u) ->
               let uu____6089 = tc_check_tot_or_gtot_term env t k in
               (match uu____6089 with
                | (t1,uu____6103,g) ->
                    let uu____6105 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6105, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____6113 =
              let uu____6114 =
                let uu____6115 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____6115 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____6114 in
            uu____6113 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____6118 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____6118 with
           | (tc1,uu____6132,f) ->
               let uu____6134 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____6134 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____6178 =
                        let uu____6179 = FStar_Syntax_Subst.compress head3 in
                        uu____6179.FStar_Syntax_Syntax.n in
                      match uu____6178 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____6182,us) -> us
                      | uu____6188 -> [] in
                    let uu____6189 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____6189 with
                     | (uu____6210,args1) ->
                         let uu____6232 =
                           let uu____6251 = FStar_List.hd args1 in
                           let uu____6264 = FStar_List.tl args1 in
                           (uu____6251, uu____6264) in
                         (match uu____6232 with
                          | (res,args2) ->
                              let uu____6329 =
                                let uu____6338 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___91_6366  ->
                                          match uu___91_6366 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____6374 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____6374 with
                                               | (env1,uu____6386) ->
                                                   let uu____6391 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____6391 with
                                                    | (e1,uu____6403,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____6338
                                  FStar_List.unzip in
                              (match uu____6329 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___109_6442 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___109_6442.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___109_6442.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____6446 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____6446 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____6450 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____6450))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____6458 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____6459 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____6469 = aux u3 in FStar_Syntax_Syntax.U_succ uu____6469
        | FStar_Syntax_Syntax.U_max us ->
            let uu____6473 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____6473
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____6478 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____6478 FStar_Pervasives_Native.snd
         | uu____6487 -> aux u)
and tc_abs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail msg t =
            let uu____6511 =
              let uu____6512 =
                let uu____6517 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____6517, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____6512 in
            FStar_Exn.raise uu____6511 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____6607 bs2 bs_expected1 =
              match uu____6607 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____6775)) ->
                             let uu____6780 =
                               let uu____6781 =
                                 let uu____6786 =
                                   let uu____6787 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____6787 in
                                 let uu____6788 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____6786, uu____6788) in
                               FStar_Errors.Error uu____6781 in
                             FStar_Exn.raise uu____6780
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____6789),FStar_Pervasives_Native.None ) ->
                             let uu____6794 =
                               let uu____6795 =
                                 let uu____6800 =
                                   let uu____6801 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____6801 in
                                 let uu____6802 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____6800, uu____6802) in
                               FStar_Errors.Error uu____6795 in
                             FStar_Exn.raise uu____6794
                         | uu____6803 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____6809 =
                           let uu____6814 =
                             let uu____6815 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____6815.FStar_Syntax_Syntax.n in
                           match uu____6814 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____6822 ->
                               ((let uu____6824 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____6824
                                 then
                                   let uu____6825 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____6825
                                 else ());
                                (let uu____6827 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____6827 with
                                 | (t,uu____6839,g1) ->
                                     let g2 =
                                       let uu____6842 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____6843 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____6842
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____6843 in
                                     let g3 =
                                       let uu____6845 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____6845 in
                                     (t, g3))) in
                         match uu____6809 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___110_6873 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___110_6873.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___110_6873.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____6886 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____6886 in
                             aux (env3, (b :: out), g1, subst2) bs3
                               bs_expected2))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         g, subst1)
                   | ([],rest) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         g, subst1)) in
            aux (env1, [], FStar_TypeChecker_Rel.trivial_guard, []) bs1
              bs_expected in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____7040 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____7047 = tc_binders env1 bs in
                  match uu____7047 with
                  | (bs1,envbody,g,uu____7081) ->
                      let uu____7082 =
                        let uu____7095 =
                          let uu____7096 = FStar_Syntax_Subst.compress body1 in
                          uu____7096.FStar_Syntax_Syntax.n in
                        match uu____7095 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____7114) ->
                            let uu____7161 = tc_comp envbody c in
                            (match uu____7161 with
                             | (c1,uu____7181,g') ->
                                 let uu____7183 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____7186 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((FStar_Pervasives_Native.Some c1),
                                   uu____7183, body1, uu____7186))
                        | uu____7191 ->
                            (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None, body1, g) in
                      (match uu____7082 with
                       | (copt,tacopt,body2,g1) ->
                           (FStar_Pervasives_Native.None, bs1, [], copt,
                             tacopt, envbody, body2, g1))))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____7279 =
                    let uu____7280 = FStar_Syntax_Subst.compress t2 in
                    uu____7280.FStar_Syntax_Syntax.n in
                  match uu____7279 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____7307 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7329 -> failwith "Impossible");
                       (let uu____7336 = tc_binders env1 bs in
                        match uu____7336 with
                        | (bs1,envbody,g,uu____7372) ->
                            let uu____7373 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____7373 with
                             | (envbody1,uu____7405) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____7418;
                         FStar_Syntax_Syntax.pos = uu____7419;
                         FStar_Syntax_Syntax.vars = uu____7420;_},uu____7421)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7463 -> failwith "Impossible");
                       (let uu____7470 = tc_binders env1 bs in
                        match uu____7470 with
                        | (bs1,envbody,g,uu____7506) ->
                            let uu____7507 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____7507 with
                             | (envbody1,uu____7539) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____7553) ->
                      let uu____7558 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____7558 with
                       | (uu____7607,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, tacopt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____7657 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____7657 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____7761 c_expected2 =
                               match uu____7761 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____7876 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____7876)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____7907 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____7907 in
                                        let uu____7908 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____7908)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        if FStar_Syntax_Util.is_named_tot c
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env3
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____7980 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____7980 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8001 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8001 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8049 =
                                                           let uu____8080 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8080,
                                                             subst2) in
                                                         handle_more
                                                           uu____8049
                                                           c_expected4))
                                           | uu____8097 ->
                                               let uu____8098 =
                                                 let uu____8099 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____8099 in
                                               fail uu____8098 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____8129 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____8129 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___111_8188 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___111_8188.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___111_8188.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___111_8188.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___111_8188.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___111_8188.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___111_8188.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___111_8188.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___111_8188.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___111_8188.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___111_8188.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___111_8188.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___111_8188.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___111_8188.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___111_8188.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___111_8188.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___111_8188.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___111_8188.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___111_8188.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___111_8188.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___111_8188.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___111_8188.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___111_8188.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___111_8188.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___111_8188.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___111_8188.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___111_8188.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___111_8188.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___111_8188.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___111_8188.FStar_TypeChecker_Env.identifier_info)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____8227  ->
                                     fun uu____8228  ->
                                       match (uu____8227, uu____8228) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____8273 =
                                             let uu____8280 =
                                               let uu____8281 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____8281
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____8280 t3 in
                                           (match uu____8273 with
                                            | (t4,uu____8303,uu____8304) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____8314 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___112_8317
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___112_8317.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___112_8317.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____8314 ::
                                                        letrec_binders
                                                  | uu____8318 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____8323 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____8323 with
                            | (envbody,bs1,g,c) ->
                                let uu____8378 =
                                  let uu____8385 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____8385
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____8378 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       FStar_Pervasives_Native.None,
                                       envbody2, body1, g))))
                  | uu____8440 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____8465 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____8465
                      else
                        (let uu____8467 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____8467 with
                         | (uu____8514,bs1,uu____8516,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, tacopt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____8543 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____8543 with
          | (env1,topt) ->
              ((let uu____8563 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____8563
                then
                  let uu____8564 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____8564
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____8568 = expected_function_typ1 env1 topt body in
                match uu____8568 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____8617 =
                      tc_term
                        (let uu___113_8626 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___113_8626.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___113_8626.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___113_8626.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___113_8626.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___113_8626.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___113_8626.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___113_8626.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___113_8626.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___113_8626.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___113_8626.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___113_8626.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___113_8626.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___113_8626.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___113_8626.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___113_8626.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___113_8626.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___113_8626.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___113_8626.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___113_8626.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___113_8626.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.type_of =
                             (uu___113_8626.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___113_8626.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___113_8626.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___113_8626.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___113_8626.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___113_8626.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___113_8626.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___113_8626.FStar_TypeChecker_Env.identifier_info)
                         }) body1 in
                    (match uu____8617 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____8638 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____8638
                           then
                             let uu____8639 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____8652 =
                               let uu____8653 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____8653 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____8639 uu____8652
                           else ());
                          (let uu____8655 =
                             let uu____8662 =
                               let uu____8667 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____8667) in
                             check_expected_effect
                               (let uu___114_8674 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___114_8674.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___114_8674.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___114_8674.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___114_8674.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___114_8674.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___114_8674.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___114_8674.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___114_8674.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___114_8674.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___114_8674.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___114_8674.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___114_8674.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___114_8674.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___114_8674.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___114_8674.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___114_8674.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___114_8674.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___114_8674.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___114_8674.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___114_8674.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___114_8674.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___114_8674.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___114_8674.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___114_8674.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___114_8674.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___114_8674.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___114_8674.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___114_8674.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___114_8674.FStar_TypeChecker_Env.identifier_info)
                                }) c_opt uu____8662 in
                           match uu____8655 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____8686 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____8688 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____8688) in
                                 if uu____8686
                                 then
                                   let uu____8689 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____8689
                                 else
                                   (let guard2 =
                                      let uu____8692 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____8692 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 FStar_Syntax_Util.abs bs1 body3
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         (FStar_Util.dflt cbody1 c_opt))) in
                               let uu____8701 =
                                 match tfun_opt with
                                 | FStar_Pervasives_Native.Some t ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____8722 -> (e, t1, guard2)
                                      | uu____8735 ->
                                          let uu____8736 =
                                            FStar_TypeChecker_Util.check_and_ascribe
                                              env1 e tfun_computed t1 in
                                          (match uu____8736 with
                                           | (e1,guard') ->
                                               let uu____8749 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____8749)))
                                 | FStar_Pervasives_Native.None  ->
                                     (e, tfun_computed, guard2) in
                               (match uu____8701 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____8763 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        FStar_Pervasives_Native.None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____8763 with
                                     | (c1,g1) -> (e1, c1, g1))))))))
and check_application_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args in
              let r = FStar_TypeChecker_Env.get_range env in
              let thead = chead.FStar_Syntax_Syntax.res_typ in
              (let uu____8812 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____8812
               then
                 let uu____8813 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____8814 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____8813
                   uu____8814
               else ());
              (let monadic_application uu____8871 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____8871 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___115_8930 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___115_8930.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___115_8930.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___115_8930.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____8931 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____8946 ->
                           let g =
                             let uu____8954 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____8954
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____8955 =
                             let uu____8956 =
                               let uu____8959 =
                                 let uu____8960 =
                                   let uu____8961 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____8961 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____8960 in
                               FStar_Syntax_Syntax.mk_Total uu____8959 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____8956 in
                           (uu____8955, g) in
                     (match uu____8931 with
                      | (cres2,guard1) ->
                          ((let uu____8975 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____8975
                            then
                              let uu____8976 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____8976
                            else ());
                           (let cres3 =
                              let uu____8979 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____8979
                              then
                                let term =
                                  FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets_rev)
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                  env term cres2
                              else cres2 in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____9013  ->
                                     match uu____9013 with
                                     | ((e,q),x,c) ->
                                         let uu____9046 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9046
                                         then
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             (FStar_Pervasives_Native.Some e)
                                             c (x, out_c)
                                         else
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             FStar_Pervasives_Native.None c
                                             (x, out_c)) cres3 arg_comps_rev in
                            let comp1 =
                              FStar_TypeChecker_Util.bind
                                head2.FStar_Syntax_Syntax.pos env
                                FStar_Pervasives_Native.None chead1
                                (FStar_Pervasives_Native.None, comp) in
                            let shortcuts_evaluation_order =
                              let uu____9058 =
                                let uu____9059 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____9059.FStar_Syntax_Syntax.n in
                              match uu____9058 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____9063 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9084  ->
                                         match uu____9084 with
                                         | (arg,uu____9098,uu____9099) -> arg
                                             :: args1) [] arg_comps_rev in
                                let app =
                                  FStar_Syntax_Syntax.mk_Tm_app head2 args1
                                    FStar_Pervasives_Native.None r in
                                let app1 =
                                  FStar_TypeChecker_Util.maybe_lift env app
                                    cres3.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.res_typ in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp1.FStar_Syntax_Syntax.eff_name
                                  comp1.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____9109 =
                                   let map_fun uu____9171 =
                                     match uu____9171 with
                                     | ((e,q),uu____9206,c) ->
                                         let uu____9216 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9216
                                         then
                                           (FStar_Pervasives_Native.None,
                                             (e, q))
                                         else
                                           (let x =
                                              FStar_Syntax_Syntax.new_bv
                                                FStar_Pervasives_Native.None
                                                c.FStar_Syntax_Syntax.res_typ in
                                            let e1 =
                                              FStar_TypeChecker_Util.maybe_lift
                                                env e
                                                c.FStar_Syntax_Syntax.eff_name
                                                comp1.FStar_Syntax_Syntax.eff_name
                                                c.FStar_Syntax_Syntax.res_typ in
                                            let uu____9266 =
                                              let uu____9271 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____9271, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____9266)) in
                                   let uu____9300 =
                                     let uu____9325 =
                                       let uu____9348 =
                                         let uu____9363 =
                                           let uu____9372 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____9372,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____9363 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____9348 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____9325 in
                                   match uu____9300 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____9545 =
                                         let uu____9546 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____9546 in
                                       let uu____9555 =
                                         let uu____9562 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____9562 in
                                       (lifted_args, uu____9545, uu____9555) in
                                 match uu____9109 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1 FStar_Pervasives_Native.None r in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let bind_lifted_args e uu___92_9665 =
                                       match uu___92_9665 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____9720 =
                                               let uu____9723 =
                                                 let uu____9724 =
                                                   let uu____9737 =
                                                     let uu____9738 =
                                                       let uu____9739 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____9739] in
                                                     FStar_Syntax_Subst.close
                                                       uu____9738 e in
                                                   ((false, [lb]),
                                                     uu____9737) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____9724 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____9723 in
                                             uu____9720
                                               FStar_Pervasives_Native.None
                                               e.FStar_Syntax_Syntax.pos in
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_meta
                                                (letbinding,
                                                  (FStar_Syntax_Syntax.Meta_monadic
                                                     (m,
                                                       (comp1.FStar_Syntax_Syntax.res_typ)))))
                                             FStar_Pervasives_Native.None
                                             e.FStar_Syntax_Syntax.pos in
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args) in
                            let uu____9769 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____9769 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____9860 bs args1 =
                 match uu____9860 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____10007))::rest,
                         (uu____10009,FStar_Pervasives_Native.None )::uu____10010)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____10071 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____10071 with
                           | (varg,uu____10091,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____10113 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____10113) in
                               let uu____10114 =
                                 let uu____10149 =
                                   let uu____10164 =
                                     let uu____10177 =
                                       let uu____10178 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____10178
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____10177) in
                                   uu____10164 :: outargs in
                                 let uu____10197 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____10149, (arg :: arg_rets),
                                   uu____10197, fvs) in
                               tc_args head_info uu____10114 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____10299),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____10300)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____10313 ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___116_10324 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___116_10324.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___116_10324.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____10326 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____10326
                             then
                               let uu____10327 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____10327
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___117_10332 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___117_10332.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___117_10332.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___117_10332.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___117_10332.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___117_10332.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___117_10332.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___117_10332.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___117_10332.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___117_10332.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___117_10332.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___117_10332.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___117_10332.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___117_10332.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___117_10332.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___117_10332.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___117_10332.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___117_10332.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___117_10332.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___117_10332.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___117_10332.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___117_10332.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___117_10332.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___117_10332.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___117_10332.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___117_10332.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___117_10332.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___117_10332.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___117_10332.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___117_10332.FStar_TypeChecker_Env.identifier_info)
                               } in
                             (let uu____10334 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____10334
                              then
                                let uu____10335 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____10336 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____10337 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____10335 uu____10336 uu____10337
                              else ());
                             (let uu____10339 = tc_term env2 e in
                              match uu____10339 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____10366 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____10366 in
                                  let uu____10367 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____10367
                                  then
                                    let subst2 =
                                      let uu____10375 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____10375
                                        e1 in
                                    tc_args head_info
                                      (subst2,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, (x1 :: fvs)) rest
                                      rest'))))
                      | (uu____10469,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____10505) ->
                          let uu____10556 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____10556 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____10590 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____10590
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____10615 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____10615 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____10638 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____10638
                                            then
                                              let uu____10639 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____10639
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____10681 when Prims.op_Negation norm1
                                     ->
                                     let uu____10682 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____10682
                                 | uu____10683 ->
                                     let uu____10684 =
                                       let uu____10685 =
                                         let uu____10690 =
                                           let uu____10691 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____10692 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____10691 uu____10692 in
                                         let uu____10699 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____10690, uu____10699) in
                                       FStar_Errors.Error uu____10685 in
                                     FStar_Exn.raise uu____10684 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____10718 =
                   let uu____10719 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____10719.FStar_Syntax_Syntax.n in
                 match uu____10718 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____10730 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____10831 = tc_term env1 e in
                           (match uu____10831 with
                            | (e1,c,g_e) ->
                                let uu____10853 = tc_args1 env1 tl1 in
                                (match uu____10853 with
                                 | (args2,comps,g_rest) ->
                                     let uu____10893 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____10893))) in
                     let uu____10914 = tc_args1 env args in
                     (match uu____10914 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____10951 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____10989  ->
                                      match uu____10989 with
                                      | (uu____11002,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____10951 in
                          let ml_or_tot t r1 =
                            let uu____11019 = FStar_Options.ml_ish () in
                            if uu____11019
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11022 =
                              let uu____11025 =
                                let uu____11026 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____11026
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____11025 in
                            ml_or_tot uu____11022 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____11039 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____11039
                            then
                              let uu____11040 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____11041 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____11042 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11040 uu____11041 uu____11042
                            else ());
                           (let uu____11045 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11045);
                           (let comp =
                              let uu____11047 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____11058  ->
                                   fun out  ->
                                     match uu____11058 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11047 in
                            let uu____11072 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11075 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11072, comp, uu____11075))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11078;
                        FStar_Syntax_Syntax.pos = uu____11079;
                        FStar_Syntax_Syntax.vars = uu____11080;_},uu____11081)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11202 = tc_term env1 e in
                           (match uu____11202 with
                            | (e1,c,g_e) ->
                                let uu____11224 = tc_args1 env1 tl1 in
                                (match uu____11224 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11264 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11264))) in
                     let uu____11285 = tc_args1 env args in
                     (match uu____11285 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11322 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11360  ->
                                      match uu____11360 with
                                      | (uu____11373,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11322 in
                          let ml_or_tot t r1 =
                            let uu____11390 = FStar_Options.ml_ish () in
                            if uu____11390
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11393 =
                              let uu____11396 =
                                let uu____11397 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____11397
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____11396 in
                            ml_or_tot uu____11393 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____11410 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____11410
                            then
                              let uu____11411 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____11412 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____11413 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11411 uu____11412 uu____11413
                            else ());
                           (let uu____11416 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11416);
                           (let comp =
                              let uu____11418 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____11429  ->
                                   fun out  ->
                                     match uu____11429 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11418 in
                            let uu____11443 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11446 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11443, comp, uu____11446))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____11467 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____11467 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____11532) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____11538,uu____11539) -> check_function_app t
                 | uu____11580 ->
                     let uu____11581 =
                       let uu____11582 =
                         let uu____11587 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____11587, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____11582 in
                     FStar_Exn.raise uu____11581 in
               check_function_app thead)
and check_short_circuit_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env in
              let tf =
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c in
                  let uu____11657 =
                    FStar_List.fold_left2
                      (fun uu____11700  ->
                         fun uu____11701  ->
                           fun uu____11702  ->
                             match (uu____11700, uu____11701, uu____11702)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____11770 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____11770 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____11788 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____11788 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____11792 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____11792)
                                              &&
                                              (let uu____11794 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____11794)) in
                                       let uu____11795 =
                                         let uu____11804 =
                                           let uu____11813 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____11813] in
                                         FStar_List.append seen uu____11804 in
                                       let uu____11820 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____11795, uu____11820, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____11657 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____11856 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____11856
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____11858 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____11858 with | (c2,g) -> (e, c2, g)))
              | uu____11875 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and tc_eqn:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 ->
        ((FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____11909 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____11909 with
        | (pattern,when_clause,branch_exp) ->
            let uu____11945 = branch1 in
            (match uu____11945 with
             | (cpat,uu____11977,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____12029 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____12029 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____12058 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____12058
                         then
                           let uu____12059 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____12060 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12059 uu____12060
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____12063 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____12063 with
                         | (env1,uu____12083) ->
                             let env11 =
                               let uu___118_12089 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___118_12089.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___118_12089.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___118_12089.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___118_12089.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___118_12089.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___118_12089.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___118_12089.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___118_12089.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___118_12089.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___118_12089.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___118_12089.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___118_12089.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___118_12089.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___118_12089.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___118_12089.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___118_12089.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___118_12089.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___118_12089.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___118_12089.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___118_12089.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___118_12089.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___118_12089.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___118_12089.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___118_12089.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___118_12089.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___118_12089.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___118_12089.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___118_12089.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___118_12089.FStar_TypeChecker_Env.identifier_info)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____12092 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____12092
                               then
                                 let uu____12093 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____12094 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12093 uu____12094
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____12097 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____12097 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___119_12120 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___119_12120.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___119_12120.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___119_12120.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____12121 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g' in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let uu____12125 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2 in
                                     FStar_All.pipe_right uu____12125
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____12142 =
                                       let uu____12143 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____12143 in
                                     if uu____12142
                                     then
                                       let unresolved =
                                         let uu____12155 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____12155
                                           FStar_Util.set_elements in
                                       let uu____12182 =
                                         let uu____12183 =
                                           let uu____12188 =
                                             let uu____12189 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____12190 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____12191 =
                                               let uu____12192 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____12210  ->
                                                         match uu____12210
                                                         with
                                                         | (u,uu____12216) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____12192
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____12189 uu____12190
                                               uu____12191 in
                                           (uu____12188,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____12183 in
                                       FStar_Exn.raise uu____12182
                                     else ());
                                    (let uu____12221 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____12221
                                     then
                                       let uu____12222 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____12222
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____12231 =
                   let uu____12238 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____12238
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____12231 with
                  | (scrutinee_env,uu____12262) ->
                      let uu____12267 = tc_pat true pat_t pattern in
                      (match uu____12267 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____12305 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____12327 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____12327
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____12341 =
                                      let uu____12348 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____12348 e in
                                    match uu____12341 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____12305 with
                            | (when_clause1,g_when) ->
                                let uu____12382 = tc_term pat_env branch_exp in
                                (match uu____12382 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____12414 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_42  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_42) uu____12414 in
                                     let uu____12417 =
                                       let eqs =
                                         let uu____12427 =
                                           let uu____12428 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____12428 in
                                         if uu____12427
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____12435 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____12452 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____12453 ->
                                                FStar_Pervasives_Native.None
                                            | uu____12454 ->
                                                let uu____12455 =
                                                  let uu____12456 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____12456 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____12455) in
                                       let uu____12457 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____12457 with
                                       | (c1,g_branch1) ->
                                           let uu____12472 =
                                             match (eqs, when_condition) with
                                             | uu____12485 when
                                                 let uu____12494 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____12494
                                                 -> (c1, g_when)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.None
                                                ) -> (c1, g_when)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.None
                                                ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____12506 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____12507 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____12506, uu____12507)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____12516 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____12516 in
                                                 let uu____12517 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____12518 =
                                                   let uu____12519 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____12519 g_when in
                                                 (uu____12517, uu____12518)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____12527 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____12527, g_when) in
                                           (match uu____12472 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____12539 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____12540 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____12539, uu____12540,
                                                  g_branch1)) in
                                     (match uu____12417 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____12561 =
                                              let uu____12562 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____12562 in
                                            if uu____12561
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____12592 =
                                                     let uu____12593 =
                                                       let uu____12594 =
                                                         let uu____12597 =
                                                           let uu____12604 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____12604 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____12597 in
                                                       FStar_List.length
                                                         uu____12594 in
                                                     uu____12593 >
                                                       (Prims.parse_int "1") in
                                                   if uu____12592
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____12610 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____12610 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____12631 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____12646 =
                                                             let uu____12647
                                                               =
                                                               let uu____12648
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____12648] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____12647 in
                                                           uu____12646
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____12651 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____12651]
                                                   else [] in
                                                 let fail uu____12656 =
                                                   let uu____12657 =
                                                     let uu____12658 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____12659 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____12660 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____12658
                                                       uu____12659
                                                       uu____12660 in
                                                   failwith uu____12657 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____12671) ->
                                                       head_constructor t1
                                                   | uu____12676 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____12678 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____12678
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____12681 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____12698;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____12699;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____12700;_},uu____12701)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____12738 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____12740 =
                                                       let uu____12741 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____12741
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____12740]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____12742 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____12750 =
                                                       let uu____12751 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____12751 in
                                                     if uu____12750
                                                     then []
                                                     else
                                                       (let uu____12755 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____12755)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____12758 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____12760 =
                                                       let uu____12761 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____12761 in
                                                     if uu____12760
                                                     then []
                                                     else
                                                       (let uu____12765 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____12765)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____12791 =
                                                       let uu____12792 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____12792 in
                                                     if uu____12791
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____12799 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____12831
                                                                     ->
                                                                    match uu____12831
                                                                    with
                                                                    | 
                                                                    (ei,uu____12841)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____12847
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____12847
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____12868
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____12882
                                                                    =
                                                                    let uu____12883
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____12884
                                                                    =
                                                                    let uu____12885
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____12885] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____12883
                                                                    uu____12884 in
                                                                    uu____12882
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____12799
                                                            FStar_List.flatten in
                                                        let uu____12894 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____12894
                                                          sub_term_guards)
                                                 | uu____12897 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____12909 =
                                                   let uu____12910 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____12910 in
                                                 if uu____12909
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____12913 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____12913 in
                                                    let uu____12918 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____12918 with
                                                    | (k,uu____12924) ->
                                                        let uu____12925 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____12925
                                                         with
                                                         | (t1,uu____12933,uu____12934)
                                                             -> t1)) in
                                               let branch_guard =
                                                 build_and_check_branch_guard
                                                   scrutinee_tm norm_pat_exp in
                                               let branch_guard1 =
                                                 match when_condition with
                                                 | FStar_Pervasives_Native.None
                                                      -> branch_guard
                                                 | FStar_Pervasives_Native.Some
                                                     w ->
                                                     FStar_Syntax_Util.mk_conj
                                                       branch_guard w in
                                               branch_guard1) in
                                          let guard =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when1 g_branch1 in
                                          ((let uu____12940 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____12940
                                            then
                                              let uu____12941 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____12941
                                            else ());
                                           (let uu____12943 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____12943, branch_guard, c1,
                                              guard)))))))))
and check_top_level_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____12969 = check_let_bound_def true env1 lb in
          (match uu____12969 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____12991 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13008 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____13008, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13011 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____13011
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____13015 =
                      let uu____13024 =
                        let uu____13035 =
                          let uu____13044 =
                            let uu____13057 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13057) in
                          [uu____13044] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13035 in
                      FStar_List.hd uu____13024 in
                    match uu____13015 with
                    | (uu____13106,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____12991 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____13120 =
                      let uu____13127 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____13127
                      then
                        let uu____13134 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____13134 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____13157 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____13157
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____13158 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____13158, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____13168 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____13168
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____13176 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____13176
                            then e2
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta
                                   (e2,
                                     (FStar_Syntax_Syntax.Meta_desugared
                                        FStar_Syntax_Syntax.Masked_effect)))
                                FStar_Pervasives_Native.None
                                e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____13120 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_Syntax_Syntax.t_unit in
                         let lb1 =
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             lb.FStar_Syntax_Syntax.lbname univ_vars2
                             (FStar_Syntax_Util.comp_result c12)
                             (FStar_Syntax_Util.comp_effect_name c12) e11 in
                         let uu____13200 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         (uu____13200,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____13215 -> failwith "Impossible"
and check_inner_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___120_13246 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___120_13246.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___120_13246.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___120_13246.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___120_13246.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___120_13246.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___120_13246.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___120_13246.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___120_13246.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___120_13246.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___120_13246.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___120_13246.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___120_13246.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___120_13246.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___120_13246.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___120_13246.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___120_13246.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___120_13246.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___120_13246.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___120_13246.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___120_13246.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___120_13246.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.type_of =
                (uu___120_13246.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___120_13246.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___120_13246.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___120_13246.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___120_13246.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___120_13246.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___120_13246.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___120_13246.FStar_TypeChecker_Env.identifier_info)
            } in
          let uu____13247 =
            let uu____13258 =
              let uu____13259 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____13259 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____13258 lb in
          (match uu____13247 with
           | (e1,uu____13281,c1,g1,annotated) ->
               let x =
                 let uu___121_13286 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___121_13286.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___121_13286.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____13287 =
                 let uu____13292 =
                   let uu____13293 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____13293] in
                 FStar_Syntax_Subst.open_term uu____13292 e2 in
               (match uu____13287 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____13312 =
                      let uu____13319 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____13319 e21 in
                    (match uu____13312 with
                     | (e22,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind
                             e1.FStar_Syntax_Syntax.pos env2
                             (FStar_Pervasives_Native.Some e1) c1
                             ((FStar_Pervasives_Native.Some x1), c2) in
                         let e11 =
                           FStar_TypeChecker_Util.maybe_lift env2 e1
                             c1.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c1.FStar_Syntax_Syntax.res_typ in
                         let e23 =
                           FStar_TypeChecker_Util.maybe_lift env2 e22
                             c2.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c2.FStar_Syntax_Syntax.res_typ in
                         let lb1 =
                           FStar_Syntax_Util.mk_letbinding
                             (FStar_Util.Inl x1) []
                             c1.FStar_Syntax_Syntax.res_typ
                             c1.FStar_Syntax_Syntax.eff_name e11 in
                         let e3 =
                           let uu____13338 =
                             let uu____13341 =
                               let uu____13342 =
                                 let uu____13355 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____13355) in
                               FStar_Syntax_Syntax.Tm_let uu____13342 in
                             FStar_Syntax_Syntax.mk uu____13341 in
                           uu____13338 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____13369 =
                             let uu____13370 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____13371 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____13370
                               c1.FStar_Syntax_Syntax.res_typ uu____13371 e11 in
                           FStar_All.pipe_left
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.NonTrivial _0_43)
                             uu____13369 in
                         let g21 =
                           let uu____13373 =
                             let uu____13374 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____13374 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____13373 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____13376 =
                           let uu____13377 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____13377 in
                         if uu____13376
                         then
                           let tt =
                             let uu____13387 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____13387
                               FStar_Option.get in
                           ((let uu____13393 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____13393
                             then
                               let uu____13394 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____13395 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____13394 uu____13395
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____13400 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____13400
                             then
                               let uu____13401 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____13402 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____13401 uu____13402
                             else ());
                            (e4,
                              ((let uu___122_13405 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___122_13405.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___122_13405.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___122_13405.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____13406 -> failwith "Impossible"
and check_top_level_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____13438 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____13438 with
           | (lbs1,e21) ->
               let uu____13457 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____13457 with
                | (env0,topt) ->
                    let uu____13476 = build_let_rec_env true env0 lbs1 in
                    (match uu____13476 with
                     | (lbs2,rec_env) ->
                         let uu____13495 = check_let_recs rec_env lbs2 in
                         (match uu____13495 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____13515 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____13515
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____13521 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____13521
                                  (fun _0_44  ->
                                     FStar_Pervasives_Native.Some _0_44) in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef in
                                          if
                                            lb.FStar_Syntax_Syntax.lbunivs =
                                              []
                                          then lb
                                          else
                                            FStar_Syntax_Util.close_univs_and_mk_letbinding
                                              all_lb_names
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef))
                                else
                                  (let ecs =
                                     let uu____13566 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____13606 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____13606))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____13566 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____13646  ->
                                           match uu____13646 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____13684 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____13684 in
                              let uu____13689 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____13689 with
                               | (lbs5,e22) ->
                                   ((let uu____13709 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____13709
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____13710 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____13710, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____13723 -> failwith "Impossible"
and check_inner_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____13755 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____13755 with
           | (lbs1,e21) ->
               let uu____13774 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____13774 with
                | (env0,topt) ->
                    let uu____13793 = build_let_rec_env false env0 lbs1 in
                    (match uu____13793 with
                     | (lbs2,rec_env) ->
                         let uu____13812 = check_let_recs rec_env lbs2 in
                         (match uu____13812 with
                          | (lbs3,g_lbs) ->
                              let uu____13831 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___123_13854 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___123_13854.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___123_13854.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___124_13856 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___124_13856.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___124_13856.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___124_13856.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___124_13856.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____13831 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____13883 = tc_term env2 e21 in
                                   (match uu____13883 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____13900 =
                                            let uu____13901 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____13901 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____13900 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___125_13905 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___125_13905.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___125_13905.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___125_13905.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____13906 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____13906 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____13942 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___126_13947 =
                                                      cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___126_13947.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___126_13947.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___126_13947.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____13950 -> failwith "Impossible"
and build_let_rec_env:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env in
        let termination_check_enabled lbname lbdef lbtyp =
          let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
          let uu____13980 =
            let uu____13985 =
              let uu____13986 = FStar_Syntax_Subst.compress t in
              uu____13986.FStar_Syntax_Syntax.n in
            let uu____13989 =
              let uu____13990 = FStar_Syntax_Subst.compress lbdef in
              uu____13990.FStar_Syntax_Syntax.n in
            (uu____13985, uu____13989) in
          match uu____13980 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____13996,uu____13997)) ->
              let actuals1 =
                let uu____14035 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____14035
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____14056 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____14056) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____14074 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____14074) in
                  let msg =
                    let uu____14082 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____14083 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____14082 uu____14083 formals_msg actuals_msg in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____14090 ->
              let uu____14095 =
                let uu____14096 =
                  let uu____14101 =
                    let uu____14102 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____14103 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____14102 uu____14103 in
                  (uu____14101, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____14096 in
              FStar_Exn.raise uu____14095 in
        let uu____14104 =
          FStar_List.fold_left
            (fun uu____14130  ->
               fun lb  ->
                 match uu____14130 with
                 | (lbs1,env1) ->
                     let uu____14150 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____14150 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1 in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let t1 =
                            if Prims.op_Negation check_t
                            then t
                            else
                              (let uu____14170 =
                                 let uu____14177 =
                                   let uu____14178 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____14178 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___127_14189 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___127_14189.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___127_14189.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___127_14189.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___127_14189.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___127_14189.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___127_14189.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___127_14189.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___127_14189.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___127_14189.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___127_14189.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___127_14189.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___127_14189.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___127_14189.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___127_14189.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___127_14189.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___127_14189.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___127_14189.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___127_14189.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___127_14189.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___127_14189.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___127_14189.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___127_14189.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___127_14189.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___127_14189.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___127_14189.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___127_14189.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___127_14189.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___127_14189.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___127_14189.FStar_TypeChecker_Env.identifier_info)
                                    }) t uu____14177 in
                               match uu____14170 with
                               | (t1,uu____14191,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____14195 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____14195);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____14197 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____14197
                            then
                              let uu___128_14198 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___128_14198.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___128_14198.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___128_14198.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___128_14198.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___128_14198.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___128_14198.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___128_14198.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___128_14198.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___128_14198.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___128_14198.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___128_14198.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___128_14198.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___128_14198.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___128_14198.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___128_14198.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___128_14198.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___128_14198.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___128_14198.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___128_14198.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___128_14198.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___128_14198.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___128_14198.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___128_14198.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___128_14198.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___128_14198.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___128_14198.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___128_14198.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___128_14198.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___128_14198.FStar_TypeChecker_Env.identifier_info)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___129_14215 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___129_14215.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___129_14215.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____14104 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____14238 =
        let uu____14247 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____14276 =
                     let uu____14277 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____14277.FStar_Syntax_Syntax.n in
                   match uu____14276 with
                   | FStar_Syntax_Syntax.Tm_abs uu____14280 -> ()
                   | uu____14297 ->
                       let uu____14298 =
                         let uu____14299 =
                           let uu____14304 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____14304) in
                         FStar_Errors.Error uu____14299 in
                       FStar_Exn.raise uu____14298);
                  (let uu____14305 =
                     let uu____14312 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____14312
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____14305 with
                   | (e,c,g) ->
                       ((let uu____14321 =
                           let uu____14322 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____14322 in
                         if uu____14321
                         then
                           FStar_Exn.raise
                             (FStar_Errors.Error
                                ("Expected let rec to be a Tot term; got effect GTot",
                                  (e.FStar_Syntax_Syntax.pos)))
                         else ());
                        (let lb1 =
                           FStar_Syntax_Util.mk_letbinding
                             lb.FStar_Syntax_Syntax.lbname
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbtyp
                             FStar_Parser_Const.effect_Tot_lid e in
                         (lb1, g)))))) in
        FStar_All.pipe_right uu____14247 FStar_List.unzip in
      match uu____14238 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs
              FStar_TypeChecker_Rel.trivial_guard in
          (lbs1, g_lbs)
and check_let_bound_def:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t,Prims.bool)
          FStar_Pervasives_Native.tuple5
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____14371 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____14371 with
        | (env1,uu____14389) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____14397 = check_lbtyp top_level env lb in
            (match uu____14397 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____14441 =
                     tc_maybe_toplevel_term
                       (let uu___130_14450 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___130_14450.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___130_14450.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___130_14450.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___130_14450.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___130_14450.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___130_14450.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___130_14450.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___130_14450.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___130_14450.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___130_14450.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___130_14450.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___130_14450.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___130_14450.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___130_14450.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___130_14450.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___130_14450.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___130_14450.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___130_14450.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___130_14450.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___130_14450.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___130_14450.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.type_of =
                            (uu___130_14450.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___130_14450.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___130_14450.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___130_14450.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___130_14450.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___130_14450.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___130_14450.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___130_14450.FStar_TypeChecker_Env.identifier_info)
                        }) e11 in
                   match uu____14441 with
                   | (e12,c1,g1) ->
                       let uu____14464 =
                         let uu____14469 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____14473  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____14469 e12 c1 wf_annot in
                       (match uu____14464 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____14488 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____14488
                              then
                                let uu____14489 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____14490 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____14491 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____14489 uu____14490 uu____14491
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))
and check_lbtyp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_TypeChecker_Env.guard_t,
          FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.subst_elt
                                           Prims.list,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple5
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            (if lb.FStar_Syntax_Syntax.lbunivs <> []
             then
               failwith
                 "Impossible: non-empty universe variables but the type is unknown"
             else ();
             (FStar_Pervasives_Native.None,
               FStar_TypeChecker_Rel.trivial_guard, [], [], env))
        | uu____14535 ->
            let uu____14536 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____14536 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14585 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____14585)
                 else
                   (let uu____14593 = FStar_Syntax_Util.type_u () in
                    match uu____14593 with
                    | (k,uu____14613) ->
                        let uu____14614 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____14614 with
                         | (t2,uu____14636,g) ->
                             ((let uu____14639 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____14639
                               then
                                 let uu____14640 =
                                   let uu____14641 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____14641 in
                                 let uu____14642 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____14640 uu____14642
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____14645 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____14645))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____14653  ->
      match uu____14653 with
      | (x,imp) ->
          let uu____14672 = FStar_Syntax_Util.type_u () in
          (match uu____14672 with
           | (tu,u) ->
               ((let uu____14692 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____14692
                 then
                   let uu____14693 = FStar_Syntax_Print.bv_to_string x in
                   let uu____14694 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____14695 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____14693 uu____14694 uu____14695
                 else ());
                (let uu____14697 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____14697 with
                 | (t,uu____14717,g) ->
                     let x1 =
                       ((let uu___131_14725 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___131_14725.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___131_14725.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____14727 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____14727
                       then
                         let uu____14728 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____14729 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____14728 uu____14729
                       else ());
                      (let uu____14731 = push_binding env x1 in
                       (x1, uu____14731, g, u))))))
and tc_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____14821 = tc_binder env1 b in
            (match uu____14821 with
             | (b1,env',g,u) ->
                 let uu____14862 = aux env' bs2 in
                 (match uu____14862 with
                  | (bs3,env'1,g',us) ->
                      let uu____14915 =
                        let uu____14916 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____14916 in
                      ((b1 :: bs3), env'1, uu____14915, (u :: us)))) in
      aux env bs
and tc_pats:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____15001  ->
             fun uu____15002  ->
               match (uu____15001, uu____15002) with
               | ((t,imp),(args1,g)) ->
                   let uu____15071 = tc_term env1 t in
                   (match uu____15071 with
                    | (t1,uu____15089,g') ->
                        let uu____15091 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____15091))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____15133  ->
             match uu____15133 with
             | (pats1,g) ->
                 let uu____15158 = tc_args env p in
                 (match uu____15158 with
                  | (args,g') ->
                      let uu____15171 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____15171))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____15184 = tc_maybe_toplevel_term env e in
      match uu____15184 with
      | (e1,c,g) ->
          let uu____15200 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____15200
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____15213 =
               let uu____15218 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____15218
               then
                 let uu____15223 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____15223, false)
               else
                 (let uu____15225 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____15225, true)) in
             match uu____15213 with
             | (target_comp,allow_ghost) ->
                 let uu____15234 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____15234 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____15244 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____15244)
                  | uu____15245 ->
                      if allow_ghost
                      then
                        let uu____15254 =
                          let uu____15255 =
                            let uu____15260 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____15260, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____15255 in
                        FStar_Exn.raise uu____15254
                      else
                        (let uu____15268 =
                           let uu____15269 =
                             let uu____15274 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____15274, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____15269 in
                         FStar_Exn.raise uu____15268)))
and tc_check_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
        tc_tot_or_gtot_term env1 e
and tc_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____15293 = tc_tot_or_gtot_term env t in
      match uu____15293 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let type_of_tot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      (let uu____15323 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15323
       then
         let uu____15324 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____15324
       else ());
      (let env1 =
         let uu___132_15327 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___132_15327.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___132_15327.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___132_15327.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___132_15327.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___132_15327.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___132_15327.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___132_15327.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___132_15327.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___132_15327.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___132_15327.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___132_15327.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___132_15327.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___132_15327.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___132_15327.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___132_15327.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___132_15327.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___132_15327.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___132_15327.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___132_15327.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___132_15327.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.type_of =
             (uu___132_15327.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___132_15327.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___132_15327.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___132_15327.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___132_15327.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___132_15327.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___132_15327.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___132_15327.FStar_TypeChecker_Env.identifier_info)
         } in
       let uu____15332 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____15365) ->
             let uu____15366 =
               let uu____15367 =
                 let uu____15372 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____15372) in
               FStar_Errors.Error uu____15367 in
             FStar_Exn.raise uu____15366 in
       match uu____15332 with
       | (t,c,g) ->
           let uu____15388 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____15388
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____15398 =
                let uu____15399 =
                  let uu____15404 =
                    let uu____15405 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____15405 in
                  let uu____15406 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____15404, uu____15406) in
                FStar_Errors.Error uu____15399 in
              FStar_Exn.raise uu____15398))
let level_of_type_fail:
  'Auu____15421 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____15421
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____15434 =
          let uu____15435 =
            let uu____15440 =
              let uu____15441 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Expected a term of type 'Type'; got %s : %s" uu____15441 t in
            let uu____15442 = FStar_TypeChecker_Env.get_range env in
            (uu____15440, uu____15442) in
          FStar_Errors.Error uu____15435 in
        FStar_Exn.raise uu____15434
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____15462 =
            let uu____15463 = FStar_Syntax_Util.unrefine t1 in
            uu____15463.FStar_Syntax_Syntax.n in
          match uu____15462 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____15467 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____15470 = FStar_Syntax_Util.type_u () in
                 match uu____15470 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___135_15478 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___135_15478.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___135_15478.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___135_15478.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___135_15478.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___135_15478.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___135_15478.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___135_15478.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___135_15478.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___135_15478.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___135_15478.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___135_15478.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___135_15478.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___135_15478.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___135_15478.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___135_15478.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___135_15478.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___135_15478.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___135_15478.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___135_15478.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___135_15478.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___135_15478.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.type_of =
                           (uu___135_15478.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___135_15478.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___135_15478.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___135_15478.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___135_15478.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___135_15478.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___135_15478.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___135_15478.FStar_TypeChecker_Env.identifier_info)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____15482 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____15482
                       | uu____15483 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec universe_of_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun e  ->
      let uu____15494 =
        let uu____15495 = FStar_Syntax_Subst.compress e in
        uu____15495.FStar_Syntax_Syntax.n in
      match uu____15494 with
      | FStar_Syntax_Syntax.Tm_bvar uu____15500 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____15505 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____15532 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____15548) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____15571,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____15598) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____15605 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____15605 with | ((uu____15616,t),uu____15618) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____15623,(FStar_Util.Inl t,uu____15625),uu____15626) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____15673,(FStar_Util.Inr c,uu____15675),uu____15676) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____15726;
             FStar_Syntax_Syntax.vars = uu____15727;_},us)
          ->
          let uu____15733 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____15733 with
           | ((us',t),uu____15746) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____15752 =
                     let uu____15753 =
                       let uu____15758 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____15758) in
                     FStar_Errors.Error uu____15753 in
                   FStar_Exn.raise uu____15752)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____15774 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____15775 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____15785) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____15808 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____15808 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____15828  ->
                      match uu____15828 with
                      | (b,uu____15834) ->
                          let uu____15835 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____15835) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____15840 = universe_of_aux env res in
                 level_of_type env res uu____15840 in
               let u_c =
                 let uu____15842 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____15842 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____15846 = universe_of_aux env trepr in
                     level_of_type env trepr uu____15846 in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2 in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____15939 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____15954 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____15993 ->
                let uu____15994 = universe_of_aux env hd3 in
                (uu____15994, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16007 ->
                let uu____16008 = universe_of_aux env hd3 in
                (uu____16008, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____16021 ->
                let uu____16038 = universe_of_aux env hd3 in
                (uu____16038, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____16051 ->
                let uu____16058 = universe_of_aux env hd3 in
                (uu____16058, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____16071 ->
                let uu____16098 = universe_of_aux env hd3 in
                (uu____16098, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____16111 ->
                let uu____16118 = universe_of_aux env hd3 in
                (uu____16118, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____16131 ->
                let uu____16132 = universe_of_aux env hd3 in
                (uu____16132, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____16145 ->
                let uu____16158 = universe_of_aux env hd3 in
                (uu____16158, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____16171 ->
                let uu____16178 = universe_of_aux env hd3 in
                (uu____16178, args1)
            | FStar_Syntax_Syntax.Tm_type uu____16191 ->
                let uu____16192 = universe_of_aux env hd3 in
                (uu____16192, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____16205,hd4::uu____16207) ->
                let uu____16272 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____16272 with
                 | (uu____16287,uu____16288,hd5) ->
                     let uu____16306 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____16306 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____16357 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____16359 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____16359 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____16410 ->
                let uu____16411 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____16411 with
                 | (env1,uu____16433) ->
                     let env2 =
                       let uu___136_16439 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___136_16439.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___136_16439.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___136_16439.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___136_16439.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___136_16439.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___136_16439.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___136_16439.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___136_16439.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___136_16439.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___136_16439.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___136_16439.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___136_16439.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___136_16439.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___136_16439.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___136_16439.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___136_16439.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___136_16439.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___136_16439.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___136_16439.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___136_16439.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.type_of =
                           (uu___136_16439.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___136_16439.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___136_16439.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___136_16439.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___136_16439.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___136_16439.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___136_16439.FStar_TypeChecker_Env.identifier_info)
                       } in
                     ((let uu____16441 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____16441
                       then
                         let uu____16442 =
                           let uu____16443 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____16443 in
                         let uu____16444 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____16442 uu____16444
                       else ());
                      (let uu____16446 = tc_term env2 hd3 in
                       match uu____16446 with
                       | (uu____16467,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____16468;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____16470;
                                        FStar_Syntax_Syntax.comp =
                                          uu____16471;_},g)
                           ->
                           ((let uu____16482 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____16482
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____16493 = type_of_head true hd1 args in
          (match uu____16493 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____16533 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____16533 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____16577 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____16577)))
      | FStar_Syntax_Syntax.Tm_match (uu____16580,hd1::uu____16582) ->
          let uu____16647 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____16647 with
           | (uu____16650,uu____16651,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____16669,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____16714 = universe_of_aux env e in
      level_of_type env e uu____16714
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____16735 = tc_binders env tps in
      match uu____16735 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))