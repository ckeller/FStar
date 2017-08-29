open Prims
let tc_one_file:
  Prims.string Prims.list ->
    FStar_Universal.uenv ->
      ((Prims.string FStar_Pervasives_Native.option,Prims.string)
         FStar_Pervasives_Native.tuple2,(FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
                                          FStar_Pervasives_Native.tuple2,
        Prims.string Prims.list) FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun uenv  ->
      let uu____31 = uenv in
      match uu____31 with
      | (dsenv,env) ->
          let uu____52 =
            match remaining with
            | intf::impl::remaining1 when
                FStar_Universal.needs_interleaving intf impl ->
                let uu____90 =
                  FStar_Universal.tc_one_file dsenv env
                    (FStar_Pervasives_Native.Some intf) impl in
                (match uu____90 with
                 | (uu____117,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____142 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl in
                (match uu____142 with
                 | (uu____169,dsenv1,env1) ->
                     ((FStar_Pervasives_Native.None, intf_or_impl), dsenv1,
                       env1, remaining1))
            | [] -> failwith "Impossible" in
          (match uu____52 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
let tc_prims:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    let uu____273 = FStar_Universal.tc_prims env in
    match uu____273 with | (uu____288,dsenv,env1) -> (dsenv, env1)
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
let pop:
  'Auu____317 .
    ('Auu____317,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.string -> Prims.unit
  =
  fun uu____328  ->
    fun msg  ->
      match uu____328 with
      | (uu____334,env) ->
          (FStar_Universal.pop_context env msg; FStar_Options.pop ())
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____341 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____346 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____351 -> false
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____372  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____372 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___229_387 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___229_387.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___229_387.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___229_387.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___229_387.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___229_387.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___229_387.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___229_387.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___229_387.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___229_387.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___229_387.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___229_387.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___229_387.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___229_387.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___229_387.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___229_387.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___229_387.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___229_387.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___229_387.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___229_387.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___229_387.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.type_of =
                    (uu___229_387.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___229_387.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___229_387.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___229_387.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___229_387.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___229_387.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___229_387.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___229_387.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___229_387.FStar_TypeChecker_Env.tc_hooks)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = FStar_Universal.push_context (dsenv1, tcenv1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____396 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____396 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____409  ->
    match uu____409 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark:
  'Auu____427 .
    ('Auu____427,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____439  ->
    match uu____439 with
    | (uu____444,env) ->
        let dsenv = FStar_ToSyntax_Env.reset_mark () in
        let env1 = FStar_TypeChecker_Env.reset_mark env in
        (FStar_Options.pop (); (dsenv, env1))
let cleanup:
  'Auu____453 .
    ('Auu____453,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.unit
  =
  fun uu____461  ->
    match uu____461 with
    | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____479  ->
    match uu____479 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.commit_mark dsenv in
        let env1 = FStar_TypeChecker_Env.commit_mark env in (dsenv1, env1)
let check_frag:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      (FStar_Parser_ParseIt.input_frag,Prims.bool)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,(FStar_ToSyntax_Env.env,
                                                                    FStar_TypeChecker_Env.env)
                                                                    FStar_Pervasives_Native.tuple2,
          Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option
  =
  fun uu____525  ->
    fun curmod  ->
      fun frag  ->
        match uu____525 with
        | (dsenv,env) ->
            (try
               let uu____589 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____589 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____629 =
                     let uu____642 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____642) in
                   FStar_Pervasives_Native.Some uu____629
               | uu____661 -> FStar_Pervasives_Native.None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____705 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____705 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____728 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____728 ->
                 ((let uu____730 =
                     let uu____737 =
                       let uu____742 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____742) in
                     [uu____737] in
                   FStar_TypeChecker_Err.add_errors env uu____730);
                  FStar_Pervasives_Native.None))
let deps_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____778 =
      FStar_List.partition
        (fun x  ->
           let uu____791 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____792 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____791 <> uu____792) deps in
    match uu____778 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____819 =
                  (let uu____822 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____822) ||
                    (let uu____824 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____824) in
                if uu____819
                then
                  let uu____825 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____825
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____828 ->
              ((let uu____832 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____832);
               FStar_Pervasives_Native.None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option,Prims.string,FStar_Util.time
                                                              FStar_Pervasives_Native.option,
    FStar_Util.time) FStar_Pervasives_Native.tuple4 Prims.list
let rec tc_deps:
  modul_t ->
    stack_t ->
      env_t ->
        Prims.string Prims.list ->
          m_timestamps ->
            (stack_t,env_t,m_timestamps) FStar_Pervasives_Native.tuple3
  =
  fun m  ->
    fun stack  ->
      fun env  ->
        fun remaining  ->
          fun ts  ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____887 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____906 =
                    let uu____907 = FStar_Options.lax () in
                    if uu____907 then LaxCheck else FullCheck in
                  push env uu____906 true "typecheck_modul" in
                let uu____909 = tc_one_file remaining env1 in
                (match uu____909 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____960 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____973 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____973
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____960 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
let update_deps:
  Prims.string ->
    modul_t ->
      stack_t ->
        env_t ->
          m_timestamps ->
            (stack_t,env_t,m_timestamps) FStar_Pervasives_Native.tuple3
  =
  fun filename  ->
    fun m  ->
      fun stk  ->
        fun env  ->
          fun ts  ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt = FStar_Util.get_file_last_modification_time impl in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some
                    intf1,FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> false
                 | (uu____1077,uu____1078) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1173 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1201 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1284::ts3 ->
                    (pop env1 "";
                     (let uu____1325 =
                        let uu____1340 = FStar_List.hd stack in
                        let uu____1349 = FStar_List.tl stack in
                        (uu____1340, uu____1349) in
                      match uu____1325 with
                      | ((env2,uu____1375),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1439 = ts_elt in
                  (match uu____1439 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1470 = match_dep depnames intf impl in
                       (match uu____1470 with
                        | (b,depnames') ->
                            let uu____1489 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1489
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1510 =
                                 let uu____1525 = FStar_List.hd st in
                                 let uu____1534 = FStar_List.tl st in
                                 (uu____1525, uu____1534) in
                               match uu____1510 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1611 = deps_of_our_file filename in
            match uu____1611 with
            | (filenames,uu____1627) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___216_1687  ->
    match uu___216_1687 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1691 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1691
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1693 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1696 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1714 -> true
    | uu____1719 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1735 -> uu____1735
let js_fail: 'Auu____1746 . Prims.string -> FStar_Util.json -> 'Auu____1746 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___217_1758  ->
    match uu___217_1758 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___218_1764  ->
    match uu___218_1764 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1773 .
    (FStar_Util.json -> 'Auu____1773) ->
      FStar_Util.json -> 'Auu____1773 Prims.list
  =
  fun k  ->
    fun uu___219_1786  ->
      match uu___219_1786 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___220_1804  ->
    match uu___220_1804 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1829 = js_str s in
    match uu____1829 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1830 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1835 = js_str s in
    match uu____1835 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1836 -> js_fail "reduction rule" s
type completion_kind =
  | CKSymbol
  | CKOption of Prims.bool
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2
let uu___is_CKSymbol: completion_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | CKSymbol  -> true | uu____1853 -> false
let uu___is_CKOption: completion_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____1859 -> false
let __proj__CKOption__item___0: completion_kind -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0
let uu___is_CKModuleOrNamespace: completion_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____1877 -> false
let __proj__CKModuleOrNamespace__item___0:
  completion_kind -> (Prims.bool,Prims.bool) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0
let js_optional_completion_kind:
  FStar_Util.json FStar_Pervasives_Native.option -> completion_kind =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKSymbol
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1907 = js_str k1 in
        (match uu____1907 with
         | "symbol" -> CKSymbol
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, false)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____1908 ->
             js_fail
               "completion kind (symbol, open, let-open, include, module-alias)"
               k1)
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Pop
  | Push of (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
  FStar_Pervasives_Native.tuple5
  | AutoComplete of (Prims.string,completion_kind)
  FStar_Pervasives_Native.tuple2
  | Lookup of
  (Prims.string,(Prims.string,Prims.int,Prims.int)
                  FStar_Pervasives_Native.tuple3
                  FStar_Pervasives_Native.option,Prims.string Prims.list)
  FStar_Pervasives_Native.tuple3
  | Compute of
  (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Search of Prims.string
  | MissingCurrentModule
  | ProtocolViolation of Prims.string
and query = {
  qq: query';
  qid: Prims.string;}
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1983 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1988 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1993 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1998 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____2014 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____2062 -> false
let __proj__AutoComplete__item___0:
  query' -> (Prims.string,completion_kind) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2104 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2174 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2212 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_MissingCurrentModule: query' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingCurrentModule  -> true
    | uu____2225 -> false
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2231 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
let __proj__Mkquery__item__qq: query -> query' =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qq
let __proj__Mkquery__item__qid: query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qid
let query_needs_current_module: query' -> Prims.bool =
  fun uu___221_2255  ->
    match uu___221_2255 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Pop  -> false
    | Push uu____2256 -> false
    | MissingCurrentModule  -> false
    | ProtocolViolation uu____2267 -> false
    | AutoComplete uu____2268 -> true
    | Lookup uu____2273 -> true
    | Compute uu____2290 -> true
    | Search uu____2299 -> true
let interactive_protocol_vernum: Prims.int = Prims.parse_int "2"
let interactive_protocol_features: Prims.string Prims.list =
  ["autocomplete";
  "compute";
  "describe-protocol";
  "describe-repl";
  "exit";
  "lookup";
  "lookup/documentation";
  "lookup/definition";
  "pop";
  "peek";
  "push";
  "search"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____2309 -> true
    | uu____2310 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2318 -> uu____2318
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2323 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2328 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2333 -> false
let try_assoc:
  'Auu____2342 'Auu____2343 .
    'Auu____2343 ->
      ('Auu____2343,'Auu____2342) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2342 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2366 =
        FStar_Util.try_find
          (fun uu____2380  ->
             match uu____2380 with | (k,uu____2386) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2366
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2403 =
          let uu____2404 =
            let uu____2405 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2405 in
          ProtocolViolation uu____2404 in
        { qq = uu____2403; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2432 = try_assoc key a in
      match uu____2432 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2436 =
            let uu____2437 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2437 in
          FStar_Exn.raise uu____2436 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2452 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2452 js_str in
    try
      let query =
        let uu____2461 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2461 js_str in
      let args =
        let uu____2469 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2469 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2486 = try_assoc k args in
        match uu____2486 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2494 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2495 =
              let uu____2506 =
                let uu____2507 = arg "kind" in
                FStar_All.pipe_right uu____2507 js_pushkind in
              let uu____2508 =
                let uu____2509 = arg "code" in
                FStar_All.pipe_right uu____2509 js_str in
              let uu____2510 =
                let uu____2511 = arg "line" in
                FStar_All.pipe_right uu____2511 js_int in
              let uu____2512 =
                let uu____2513 = arg "column" in
                FStar_All.pipe_right uu____2513 js_int in
              (uu____2506, uu____2508, uu____2510, uu____2512,
                (query = "peek")) in
            Push uu____2495
        | "push" ->
            let uu____2514 =
              let uu____2525 =
                let uu____2526 = arg "kind" in
                FStar_All.pipe_right uu____2526 js_pushkind in
              let uu____2527 =
                let uu____2528 = arg "code" in
                FStar_All.pipe_right uu____2528 js_str in
              let uu____2529 =
                let uu____2530 = arg "line" in
                FStar_All.pipe_right uu____2530 js_int in
              let uu____2531 =
                let uu____2532 = arg "column" in
                FStar_All.pipe_right uu____2532 js_int in
              (uu____2525, uu____2527, uu____2529, uu____2531,
                (query = "peek")) in
            Push uu____2514
        | "autocomplete" ->
            let uu____2533 =
              let uu____2538 =
                let uu____2539 = arg "partial-symbol" in
                FStar_All.pipe_right uu____2539 js_str in
              let uu____2540 =
                let uu____2541 = try_arg "kind" in
                FStar_All.pipe_right uu____2541 js_optional_completion_kind in
              (uu____2538, uu____2540) in
            AutoComplete uu____2533
        | "lookup" ->
            let uu____2546 =
              let uu____2563 =
                let uu____2564 = arg "symbol" in
                FStar_All.pipe_right uu____2564 js_str in
              let uu____2565 =
                let uu____2574 =
                  let uu____2583 = try_arg "location" in
                  FStar_All.pipe_right uu____2583
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2574
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2641 =
                          let uu____2642 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2642 js_str in
                        let uu____2643 =
                          let uu____2644 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2644 js_int in
                        let uu____2645 =
                          let uu____2646 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2646 js_int in
                        (uu____2641, uu____2643, uu____2645))) in
              let uu____2647 =
                let uu____2650 = arg "requested-info" in
                FStar_All.pipe_right uu____2650 (js_list js_str) in
              (uu____2563, uu____2565, uu____2647) in
            Lookup uu____2546
        | "compute" ->
            let uu____2663 =
              let uu____2672 =
                let uu____2673 = arg "term" in
                FStar_All.pipe_right uu____2673 js_str in
              let uu____2674 =
                let uu____2679 = try_arg "rules" in
                FStar_All.pipe_right uu____2679
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2672, uu____2674) in
            Compute uu____2663
        | "search" ->
            let uu____2694 =
              let uu____2695 = arg "terms" in
              FStar_All.pipe_right uu____2695 js_str in
            Search uu____2694
        | uu____2696 ->
            let uu____2697 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2697 in
      { qq = uu____2494; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____2711 = FStar_Util.read_line stream in
      match uu____2711 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2715 = FStar_Util.json_of_string line in
          (match uu____2715 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option_value:
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___222_2728  ->
    match uu___222_2728 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____2736 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____2736
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt:
  'Auu____2745 .
    ('Auu____2745 -> FStar_Util.json) ->
      'Auu____2745 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2763 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2763
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2770 =
      let uu____2773 =
        let uu____2774 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2774 in
      let uu____2775 =
        let uu____2778 =
          let uu____2779 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2779 in
        [uu____2778] in
      uu____2773 :: uu____2775 in
    FStar_Util.JsonList uu____2770
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2792 =
          let uu____2799 =
            let uu____2806 =
              let uu____2811 = json_of_pos b in ("beg", uu____2811) in
            let uu____2812 =
              let uu____2819 =
                let uu____2824 = json_of_pos e in ("end", uu____2824) in
              [uu____2819] in
            uu____2806 :: uu____2812 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2799 in
        FStar_Util.JsonAssoc uu____2792
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2845 = FStar_Range.file_of_use_range r in
    let uu____2846 = FStar_Range.start_of_use_range r in
    let uu____2847 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2845 uu____2846 uu____2847
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2852 = FStar_Range.file_of_range r in
    let uu____2853 = FStar_Range.start_of_range r in
    let uu____2854 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2852 uu____2853 uu____2854
let json_of_issue_level: FStar_Errors.issue_level -> FStar_Util.json =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
let json_of_issue: FStar_Errors.issue -> FStar_Util.json =
  fun issue  ->
    let uu____2863 =
      let uu____2870 =
        let uu____2877 =
          let uu____2884 =
            let uu____2889 =
              let uu____2890 =
                let uu____2893 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2899 = json_of_use_range r in [uu____2899] in
                let uu____2900 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2906 = json_of_def_range r in [uu____2906]
                  | uu____2907 -> [] in
                FStar_List.append uu____2893 uu____2900 in
              FStar_Util.JsonList uu____2890 in
            ("ranges", uu____2889) in
          [uu____2884] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2877 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2870 in
    FStar_Util.JsonAssoc uu____2863
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  lr_typ: Prims.string FStar_Pervasives_Native.option;
  lr_doc: Prims.string FStar_Pervasives_Native.option;
  lr_def: Prims.string FStar_Pervasives_Native.option;}
let __proj__Mklookup_result__item__lr_name: lookup_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_name
let __proj__Mklookup_result__item__lr_def_range:
  lookup_result -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def_range
let __proj__Mklookup_result__item__lr_typ:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_typ
let __proj__Mklookup_result__item__lr_doc:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_doc
let __proj__Mklookup_result__item__lr_def:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____3059 =
      let uu____3066 =
        let uu____3073 =
          let uu____3078 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____3078) in
        let uu____3079 =
          let uu____3086 =
            let uu____3091 =
              json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42) lr.lr_typ in
            ("type", uu____3091) in
          let uu____3092 =
            let uu____3099 =
              let uu____3104 =
                json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43)
                  lr.lr_doc in
              ("documentation", uu____3104) in
            let uu____3105 =
              let uu____3112 =
                let uu____3117 =
                  json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44)
                    lr.lr_def in
                ("definition", uu____3117) in
              [uu____3112] in
            uu____3099 :: uu____3105 in
          uu____3086 :: uu____3092 in
        uu____3073 :: uu____3079 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____3066 in
    FStar_Util.JsonAssoc uu____3059
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3150 =
      FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_46  -> FStar_Util.JsonList _0_46) uu____3150 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3172 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3172);
    FStar_Util.print_raw "\n"
let write_response:
  Prims.string -> query_status -> FStar_Util.json -> Prims.unit =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation" in
        write_json
          (FStar_Util.JsonAssoc
             [("kind", (FStar_Util.JsonStr "response"));
             ("query-id", qid1);
             ("status", status1);
             ("response", response)])
let write_message: Prims.string -> FStar_Util.json -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", contents)])
let write_hello: Prims.unit -> Prims.unit =
  fun uu____3234  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3237 =
        FStar_List.map (fun _0_47  -> FStar_Util.JsonStr _0_47)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3237 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: json_of_protocol_info))
type repl_state =
  {
  repl_line: Prims.int;
  repl_column: Prims.int;
  repl_fname: Prims.string;
  repl_stack: stack_t;
  repl_curmod: modul_t;
  repl_env: env_t;
  repl_ts: m_timestamps;
  repl_stdin: FStar_Util.stream_reader;
  repl_names: FStar_Interactive_CompletionTable.table;}
let __proj__Mkrepl_state__item__repl_line: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_line
let __proj__Mkrepl_state__item__repl_column: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_column
let __proj__Mkrepl_state__item__repl_fname: repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_fname
let __proj__Mkrepl_state__item__repl_stack: repl_state -> stack_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_stack
let __proj__Mkrepl_state__item__repl_curmod: repl_state -> modul_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_curmod
let __proj__Mkrepl_state__item__repl_env: repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_env
let __proj__Mkrepl_state__item__repl_ts: repl_state -> m_timestamps =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_ts
let __proj__Mkrepl_state__item__repl_stdin:
  repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_stdin
let __proj__Mkrepl_state__item__repl_names:
  repl_state -> FStar_Interactive_CompletionTable.table =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;
        repl_names = __fname__repl_names;_} -> __fname__repl_names
type fstar_option_permission_level =
  | OptSet
  | OptReset
  | OptReadOnly
let uu___is_OptSet: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3401 -> false
let uu___is_OptReset: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3406 -> false
let uu___is_OptReadOnly: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3411 -> false
let string_of_option_permission_level:
  fstar_option_permission_level -> Prims.string =
  fun uu___223_3415  ->
    match uu___223_3415 with
    | OptSet  -> "#set-options"
    | OptReset  -> "#reset-options"
    | OptReadOnly  -> "--read-only--"
type fstar_option =
  {
  opt_name: Prims.string;
  opt_value: FStar_Options.option_val;
  opt_default: FStar_Options.option_val;
  opt_type: FStar_Options.opt_type;
  opt_snippet: Prims.string;
  opt_documentation: Prims.string FStar_Pervasives_Native.option;
  opt_permission_level: fstar_option_permission_level;}
let __proj__Mkfstar_option__item__opt_name: fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_value = __fname__opt_value;
        opt_default = __fname__opt_default; opt_type = __fname__opt_type;
        opt_snippet = __fname__opt_snippet;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_name
let __proj__Mkfstar_option__item__opt_value:
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_value = __fname__opt_value;
        opt_default = __fname__opt_default; opt_type = __fname__opt_type;
        opt_snippet = __fname__opt_snippet;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_value
let __proj__Mkfstar_option__item__opt_default:
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_value = __fname__opt_value;
        opt_default = __fname__opt_default; opt_type = __fname__opt_type;
        opt_snippet = __fname__opt_snippet;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_default
let __proj__Mkfstar_option__item__opt_type:
  fstar_option -> FStar_Options.opt_type =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_value = __fname__opt_value;
        opt_default = __fname__opt_default; opt_type = __fname__opt_type;
        opt_snippet = __fname__opt_snippet;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_type
let __proj__Mkfstar_option__item__opt_snippet: fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_value = __fname__opt_value;
        opt_default = __fname__opt_default; opt_type = __fname__opt_type;
        opt_snippet = __fname__opt_snippet;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_snippet
let __proj__Mkfstar_option__item__opt_documentation:
  fstar_option -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_value = __fname__opt_value;
        opt_default = __fname__opt_default; opt_type = __fname__opt_type;
        opt_snippet = __fname__opt_snippet;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_documentation
let __proj__Mkfstar_option__item__opt_permission_level:
  fstar_option -> fstar_option_permission_level =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_value = __fname__opt_value;
        opt_default = __fname__opt_default; opt_type = __fname__opt_type;
        opt_snippet = __fname__opt_snippet;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_permission_level
let rec kind_of_fstar_option_type: FStar_Options.opt_type -> Prims.string =
  fun uu___224_3544  ->
    match uu___224_3544 with
    | FStar_Options.Const uu____3545 -> "flag"
    | FStar_Options.IntStr uu____3546 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____3547 -> "path"
    | FStar_Options.SimpleStr uu____3548 -> "string"
    | FStar_Options.EnumStr uu____3549 -> "enum"
    | FStar_Options.OpenEnumStr uu____3552 -> "open enum"
    | FStar_Options.PostProcessed (uu____3559,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____3567,typ) ->
        kind_of_fstar_option_type typ
let rec snippet_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let uu____3581 =
        match typ with
        | FStar_Options.Const uu____3582 -> name
        | typ1 ->
            let uu____3584 =
              let uu____3587 =
                let uu____3590 =
                  let uu____3593 = FStar_Options.desc_of_opt_type typ1 in
                  [uu____3593; "}"] in
                " ${" :: uu____3590 in
              name :: uu____3587 in
            FStar_String.concat "" uu____3584 in
      Prims.strcat "--" uu____3581
let json_of_fstar_option: fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____3598 =
      let uu____3605 =
        let uu____3612 =
          let uu____3617 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____3617) in
        let uu____3618 =
          let uu____3625 =
            let uu____3630 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____3630) in
          let uu____3631 =
            let uu____3638 =
              let uu____3643 =
                json_of_opt (fun _0_48  -> FStar_Util.JsonStr _0_48)
                  opt.opt_documentation in
              ("documentation", uu____3643) in
            let uu____3644 =
              let uu____3651 =
                let uu____3656 =
                  let uu____3657 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____3657 in
                ("type", uu____3656) in
              [uu____3651;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____3638 :: uu____3644 in
          uu____3625 :: uu____3631 in
        uu____3612 :: uu____3618 in
      ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3605 in
    FStar_Util.JsonAssoc uu____3598
let fstar_options_static_cache: fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____3691 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____3720  ->
            match uu____3720 with
            | (_shortname,name,typ,doc1) ->
                let uu____3735 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____3735
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____3746 = snippet_of_fstar_option name typ in
                        let uu____3747 =
                          let uu____3748 = FStar_Options.settable name in
                          if uu____3748
                          then OptSet
                          else
                            (let uu____3750 = FStar_Options.resettable name in
                             if uu____3750 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippet = uu____3746;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____3747
                        })))) in
  FStar_All.pipe_right uu____3691
    (FStar_List.sortWith
       (fun o1  -> fun o2  -> FStar_String.compare o1.opt_name o2.opt_name))
let collect_fstar_options:
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let filter_update opt =
      let uu____3780 = filter1 opt in
      if uu____3780
      then
        let uu____3783 =
          let uu___236_3784 = opt in
          let uu____3785 = FStar_Options.get_option opt.opt_name in
          {
            opt_name = (uu___236_3784.opt_name);
            opt_value = uu____3785;
            opt_default = (uu___236_3784.opt_default);
            opt_type = (uu___236_3784.opt_type);
            opt_snippet = (uu___236_3784.opt_snippet);
            opt_documentation = (uu___236_3784.opt_documentation);
            opt_permission_level = (uu___236_3784.opt_permission_level)
          } in
        FStar_Pervasives_Native.Some uu____3783
      else FStar_Pervasives_Native.None in
    FStar_List.filter_map filter_update fstar_options_static_cache
let json_of_repl_state:
  repl_state ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun st  ->
    let uu____3797 =
      let uu____3802 =
        let uu____3803 =
          FStar_List.map
            (fun uu____3823  ->
               match uu____3823 with
               | (uu____3836,fstname,uu____3838,uu____3839) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____3803 in
      ("loaded-dependencies", uu____3802) in
    let uu____3848 =
      let uu____3855 =
        let uu____3860 =
          let uu____3861 =
            let uu____3864 = collect_fstar_options (fun uu____3869  -> true) in
            FStar_List.map json_of_fstar_option uu____3864 in
          FStar_Util.JsonList uu____3861 in
        ("options", uu____3860) in
      [uu____3855] in
    uu____3797 :: uu____3848
let with_printed_effect_args:
  'Auu____3886 . (Prims.unit -> 'Auu____3886) -> 'Auu____3886 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____3898  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____3909  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____3915  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____3922 'Auu____3923 .
    'Auu____3923 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3922,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____3954 'Auu____3955 .
    'Auu____3955 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3955,'Auu____3954) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____3984 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3984) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4001 =
      let uu____4006 =
        let uu____4007 = json_of_repl_state st in
        FStar_Util.JsonAssoc uu____4007 in
      (QueryOK, uu____4006) in
    (uu____4001, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____4030 'Auu____4031 .
    'Auu____4031 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4031,'Auu____4030) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_missing_current_module:
  'Auu____4070 'Auu____4071 'Auu____4072 .
    'Auu____4072 ->
      'Auu____4071 ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4072,'Auu____4070) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr "Current module unset")),
        (FStar_Util.Inl st))
let nothing_left_to_pop: repl_state -> Prims.bool =
  fun st  ->
    (FStar_List.length st.repl_stack) <= (FStar_List.length st.repl_ts)
let run_pop:
  'Auu____4125 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4125) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    if nothing_left_to_pop st
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (match st.repl_stack with
       | [] -> failwith "impossible"
       | (env,curmod)::stack ->
           (pop st.repl_env "#pop";
            (let st' =
               let uu___237_4194 = st in
               {
                 repl_line = (uu___237_4194.repl_line);
                 repl_column = (uu___237_4194.repl_column);
                 repl_fname = (uu___237_4194.repl_fname);
                 repl_stack = stack;
                 repl_curmod = curmod;
                 repl_env = env;
                 repl_ts = (uu___237_4194.repl_ts);
                 repl_stdin = (uu___237_4194.repl_stdin);
                 repl_names = (uu___237_4194.repl_names)
               } in
             if nothing_left_to_pop st' then cleanup env else ();
             ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))))
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple3
  | NTOpen of (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
  FStar_Pervasives_Native.tuple2
  | NTInclude of (FStar_Ident.lid,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2
  | NTBinding of FStar_TypeChecker_Env.binding
let uu___is_NTAlias: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____4246 -> false
let __proj__NTAlias__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0
let uu___is_NTOpen: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____4282 -> false
let __proj__NTOpen__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0
let uu___is_NTInclude: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____4312 -> false
let __proj__NTInclude__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0
let uu___is_NTBinding: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____4338 -> false
let __proj__NTBinding__item___0:
  name_tracking_event -> FStar_TypeChecker_Env.binding =
  fun projectee  -> match projectee with | NTBinding _0 -> _0
let query_of_ids:
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query =
  fun ids  -> FStar_List.map FStar_Ident.text_of_id ids
let query_of_lid:
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query =
  fun lid  ->
    query_of_ids
      (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident])
let update_names_from_event:
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table
  =
  fun cur_mod_str  ->
    fun table  ->
      fun evt  ->
        let is_cur_mod lid = lid.FStar_Ident.str = cur_mod_str in
        match evt with
        | NTAlias (host,id,included) ->
            if is_cur_mod host
            then
              let uu____4378 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                (FStar_Ident.text_of_id id) [] uu____4378
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____4387 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_ToSyntax_Env.Open_module) [] uu____4387
            else table
        | NTInclude (host,included) ->
            let uu____4391 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____4393 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____4391 uu____4393
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____4401) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____4403) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____4409,uu____4410) -> lids
              | uu____4415 -> [] in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     (FStar_Ident.text_of_id lid.FStar_Ident.ident)
                     (FStar_Interactive_CompletionTable.Lid lid)) table lids
let commit_name_tracking:
  modul_t ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table
  =
  fun cur_mod  ->
    fun names1  ->
      fun name_events  ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____4445 = FStar_Syntax_Syntax.mod_name md in
              uu____4445.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let fresh_name_tracking_hooks:
  Prims.unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_ToSyntax_Env.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____4464  ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____4476 =
        let uu____4479 = FStar_ST.op_Bang events in evt :: uu____4479 in
      FStar_ST.op_Colon_Equals events uu____4476 in
    (events,
      {
        FStar_ToSyntax_Env.ds_push_open_hook =
          (fun dsenv  ->
             fun op  ->
               let uu____4572 =
                 let uu____4573 =
                   let uu____4578 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____4578, op) in
                 NTOpen uu____4573 in
               push_event uu____4572);
        FStar_ToSyntax_Env.ds_push_include_hook =
          (fun dsenv  ->
             fun ns  ->
               let uu____4584 =
                 let uu____4585 =
                   let uu____4590 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____4590, ns) in
                 NTInclude uu____4585 in
               push_event uu____4584);
        FStar_ToSyntax_Env.ds_push_module_abbrev_hook =
          (fun dsenv  ->
             fun x  ->
               fun l  ->
                 let uu____4598 =
                   let uu____4599 =
                     let uu____4606 = FStar_ToSyntax_Env.current_module dsenv in
                     (uu____4606, x, l) in
                   NTAlias uu____4599 in
                 push_event uu____4598)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____4611  -> fun s  -> push_event (NTBinding s))
      })
let track_name_changes:
  env_t ->
    (env_t,env_t ->
             (env_t,name_tracking_event Prims.list)
               FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4628  ->
    match uu____4628 with
    | (dsenv,tcenv) ->
        let uu____4655 =
          let uu____4660 = FStar_ToSyntax_Env.ds_hooks dsenv in
          let uu____4661 = FStar_TypeChecker_Env.tc_hooks tcenv in
          (uu____4660, uu____4661) in
        (match uu____4655 with
         | (dsenv_old_hooks,tcenv_old_hooks) ->
             let uu____4676 = fresh_name_tracking_hooks () in
             (match uu____4676 with
              | (events,dsenv_new_hooks,tcenv_new_hooks) ->
                  let uu____4710 =
                    let uu____4715 =
                      FStar_ToSyntax_Env.set_ds_hooks dsenv dsenv_new_hooks in
                    let uu____4716 =
                      FStar_TypeChecker_Env.set_tc_hooks tcenv
                        tcenv_new_hooks in
                    (uu____4715, uu____4716) in
                  (uu____4710,
                    ((fun uu____4742  ->
                        match uu____4742 with
                        | (dsenv1,tcenv1) ->
                            let uu____4759 =
                              let uu____4764 =
                                FStar_ToSyntax_Env.set_ds_hooks dsenv1
                                  dsenv_old_hooks in
                              let uu____4765 =
                                FStar_TypeChecker_Env.set_tc_hooks tcenv1
                                  tcenv_old_hooks in
                              (uu____4764, uu____4765) in
                            let uu____4766 =
                              let uu____4769 = FStar_ST.op_Bang events in
                              FStar_List.rev uu____4769 in
                            (uu____4759, uu____4766))))))
let run_push:
  'Auu____4824 .
    repl_state ->
      push_kind ->
        Prims.string ->
          Prims.int ->
            Prims.int ->
              Prims.bool ->
                ((query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2,(repl_state,'Auu____4824)
                                                    FStar_Util.either)
                  FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun kind  ->
      fun text1  ->
        fun line  ->
          fun column  ->
            fun peek_only  ->
              let uu____4861 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
              match uu____4861 with
              | (stack,env,ts) ->
                  let uu____4883 = track_name_changes env in
                  (match uu____4883 with
                   | (env1,finish_name_tracking) ->
                       let uu____4926 =
                         if nothing_left_to_pop st
                         then
                           let uu____4947 =
                             update_deps st.repl_fname st.repl_curmod stack
                               env1 ts in
                           (true, uu____4947)
                         else (false, (stack, env1, ts)) in
                       (match uu____4926 with
                        | (restore_cmd_line_options1,(stack1,env2,ts1)) ->
                            let stack2 = (env2, (st.repl_curmod)) :: stack1 in
                            let env3 =
                              push env2 kind restore_cmd_line_options1
                                "#push" in
                            let env_marked = mark env3 in
                            let frag =
                              {
                                FStar_Parser_ParseIt.frag_text = text1;
                                FStar_Parser_ParseIt.frag_line = line;
                                FStar_Parser_ParseIt.frag_col = column
                              } in
                            let res =
                              check_frag env_marked st.repl_curmod
                                (frag, false) in
                            let errors =
                              let uu____5029 = FStar_Errors.report_all () in
                              FStar_All.pipe_right uu____5029
                                (FStar_List.map json_of_issue) in
                            (FStar_Errors.clear ();
                             (let st' =
                                let uu___238_5038 = st in
                                {
                                  repl_line = line;
                                  repl_column = column;
                                  repl_fname = (uu___238_5038.repl_fname);
                                  repl_stack = stack2;
                                  repl_curmod = (uu___238_5038.repl_curmod);
                                  repl_env = (uu___238_5038.repl_env);
                                  repl_ts = ts1;
                                  repl_stdin = (uu___238_5038.repl_stdin);
                                  repl_names = (uu___238_5038.repl_names)
                                } in
                              match res with
                              | FStar_Pervasives_Native.Some
                                  (curmod,env4,nerrs) when
                                  (nerrs = (Prims.parse_int "0")) &&
                                    (peek_only = false)
                                  ->
                                  let uu____5078 = finish_name_tracking env4 in
                                  (match uu____5078 with
                                   | (env5,name_events) ->
                                       let env6 = commit_mark env5 in
                                       let uu____5108 =
                                         let uu____5113 =
                                           let uu___239_5114 = st' in
                                           let uu____5115 =
                                             commit_name_tracking curmod
                                               st'.repl_names name_events in
                                           {
                                             repl_line =
                                               (uu___239_5114.repl_line);
                                             repl_column =
                                               (uu___239_5114.repl_column);
                                             repl_fname =
                                               (uu___239_5114.repl_fname);
                                             repl_stack =
                                               (uu___239_5114.repl_stack);
                                             repl_curmod = curmod;
                                             repl_env = env6;
                                             repl_ts =
                                               (uu___239_5114.repl_ts);
                                             repl_stdin =
                                               (uu___239_5114.repl_stdin);
                                             repl_names = uu____5115
                                           } in
                                         FStar_Util.Inl uu____5113 in
                                       ((QueryOK,
                                          (FStar_Util.JsonList errors)),
                                         uu____5108))
                              | uu____5124 ->
                                  let env4 = reset_mark env_marked in
                                  let uu____5144 = finish_name_tracking env4 in
                                  (match uu____5144 with
                                   | (env5,uu____5164) ->
                                       let uu____5169 =
                                         run_pop
                                           (let uu___240_5183 = st' in
                                            {
                                              repl_line =
                                                (uu___240_5183.repl_line);
                                              repl_column =
                                                (uu___240_5183.repl_column);
                                              repl_fname =
                                                (uu___240_5183.repl_fname);
                                              repl_stack =
                                                (uu___240_5183.repl_stack);
                                              repl_curmod =
                                                (uu___240_5183.repl_curmod);
                                              repl_env = env5;
                                              repl_ts =
                                                (uu___240_5183.repl_ts);
                                              repl_stdin =
                                                (uu___240_5183.repl_stdin);
                                              repl_names =
                                                (uu___240_5183.repl_names)
                                            }) in
                                       (match uu____5169 with
                                        | (uu____5196,st'') ->
                                            let status =
                                              if peek_only
                                              then QueryOK
                                              else QueryNOK in
                                            ((status,
                                               (FStar_Util.JsonList errors)),
                                              st'')))))))
let run_lookup:
  'Auu____5234 .
    repl_state ->
      Prims.string ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____5234) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____5283 = st.repl_env in
          match uu____5283 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____5315 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____5315 in
                let lid1 =
                  let uu____5319 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____5319 in
                let uu____5324 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____5324
                  (FStar_Util.map_option
                     (fun uu____5379  ->
                        match uu____5379 with
                        | ((uu____5398,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____5415 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____5415
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____5444 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____5444
                  (fun uu___225_5488  ->
                     match uu___225_5488 with
                     | (FStar_Util.Inr (se,uu____5510),uu____5511) ->
                         let uu____5540 = sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____5540
                     | uu____5541 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____5593  ->
                     match uu____5593 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____5640 -> info_at_pos_opt
                | FStar_Pervasives_Native.None  ->
                    if symbol = ""
                    then FStar_Pervasives_Native.None
                    else info_of_lid_str symbol in
              let response =
                match info_opt with
                | FStar_Pervasives_Native.None  ->
                    (QueryNOK, FStar_Util.JsonNull)
                | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                    let name =
                      match name_or_lid with
                      | FStar_Util.Inl name -> name
                      | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
                    let typ_str =
                      if FStar_List.mem "type" requested_info
                      then
                        let uu____5742 = term_to_string tcenv typ in
                        FStar_Pervasives_Native.Some uu____5742
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____5750 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____5761 -> FStar_Pervasives_Native.None in
                    let def_range =
                      if FStar_List.mem "defined-at" requested_info
                      then FStar_Pervasives_Native.Some rng
                      else FStar_Pervasives_Native.None in
                    let result =
                      {
                        lr_name = name;
                        lr_def_range = def_range;
                        lr_typ = typ_str;
                        lr_doc = doc_str;
                        lr_def = def_str
                      } in
                    let uu____5773 = json_of_lookup_result result in
                    (QueryOK, uu____5773) in
              (response, (FStar_Util.Inl st))
let run_autocomplete':
  'Auu____5790 .
    repl_state ->
      Prims.string ->
        (FStar_Interactive_CompletionTable.path ->
           FStar_Interactive_CompletionTable.symbol ->
             (FStar_Interactive_CompletionTable.path,FStar_Interactive_CompletionTable.symbol)
               FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
          ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____5790) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun filter1  ->
        let needle = FStar_Util.split search_term "." in
        let results =
          FStar_Interactive_CompletionTable.autocomplete st.repl_names needle
            filter1 in
        let json =
          FStar_List.map
            FStar_Interactive_CompletionTable.json_of_completion_result
            results in
        ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let run_symbol_autocomplete:
  'Auu____5860 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5860) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      let filter1 path symb =
        match (path, symb) with
        | (uu____5910,FStar_Interactive_CompletionTable.Module (true )) ->
            FStar_Pervasives_Native.None
        | (uu____5921::[],FStar_Interactive_CompletionTable.Namespace
           uu____5922) -> FStar_Pervasives_Native.None
        | path_and_symb -> FStar_Pervasives_Native.Some path_and_symb in
      run_autocomplete' st search_term filter1
let run_module_autocomplete:
  'Auu____5954 .
    repl_state ->
      Prims.string ->
        Prims.bool ->
          Prims.bool ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____5954) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun namespaces  ->
        fun modules1  ->
          let uu____5983 = st.repl_env in
          match uu____5983 with
          | (dsenv,tcenv) ->
              let rec split_last uu___226_6009 =
                match uu___226_6009 with
                | [] -> failwith "split_last on empty list"
                | h::[] -> (h, [])
                | h::t ->
                    let uu____6031 = split_last t in
                    (match uu____6031 with
                     | (last1,butlast) -> (last1, (h :: butlast))) in
              let mod_filter pred loaded path symb =
                if pred
                then
                  let uu____6085 = split_last path in
                  match uu____6085 with
                  | (last_elem,path_but_last) ->
                      let uu____6106 =
                        FStar_Interactive_CompletionTable.matched_prefix_of_path_elem
                          last_elem in
                      (match uu____6106 with
                       | FStar_Pervasives_Native.Some uu____6117 ->
                           FStar_Pervasives_Native.None
                       | uu____6124 ->
                           FStar_Pervasives_Native.Some (path_but_last, symb))
                else FStar_Pervasives_Native.None in
              let filter1 path symb =
                match symb with
                | FStar_Interactive_CompletionTable.Lid uu____6169 ->
                    FStar_Pervasives_Native.None
                | FStar_Interactive_CompletionTable.Module loaded ->
                    mod_filter modules1 loaded path symb
                | FStar_Interactive_CompletionTable.Namespace loaded ->
                    mod_filter namespaces loaded path symb in
              run_autocomplete' st search_term filter1
let candidate_of_fstar_option:
  'Auu____6186 .
    Prims.int ->
      'Auu____6186 ->
        fstar_option -> FStar_Interactive_CompletionTable.completion_result
  =
  fun match_len  ->
    fun is_reset  ->
      fun opt  ->
        let uu____6199 = kind_of_fstar_option_type opt.opt_type in
        {
          FStar_Interactive_CompletionTable.completion_match_length =
            match_len;
          FStar_Interactive_CompletionTable.completion_candidate =
            (opt.opt_snippet);
          FStar_Interactive_CompletionTable.completion_annotation =
            uu____6199
        }
let run_option_autocomplete:
  'Auu____6212 'Auu____6213 'Auu____6214 .
    'Auu____6214 ->
      Prims.string ->
        'Auu____6213 ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            ('Auu____6214,'Auu____6212) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let matcher opt = FStar_Util.starts_with opt.opt_snippet search_term in
        let options = collect_fstar_options matcher in
        let c_of_opt =
          candidate_of_fstar_option (FStar_String.length search_term)
            is_reset in
        let results = FStar_List.map c_of_opt options in
        let json =
          FStar_List.map
            FStar_Interactive_CompletionTable.json_of_completion_result
            results in
        ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let run_autocomplete:
  'Auu____6271 .
    repl_state ->
      Prims.string ->
        completion_kind ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____6271) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun kind  ->
        match kind with
        | CKSymbol  -> run_symbol_autocomplete st search_term
        | CKOption is_reset ->
            run_option_autocomplete st search_term is_reset
        | CKModuleOrNamespace (modules1,namespaces) ->
            run_module_autocomplete st search_term modules1 namespaces
let run_compute:
  'Auu____6307 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____6307) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let run_and_rewind st1 task =
          let env_marked = mark st1.repl_env in
          let results = task st1 in
          let env = reset_mark env_marked in
          let st' =
            let uu___241_6388 = st1 in
            {
              repl_line = (uu___241_6388.repl_line);
              repl_column = (uu___241_6388.repl_column);
              repl_fname = (uu___241_6388.repl_fname);
              repl_stack = (uu___241_6388.repl_stack);
              repl_curmod = (uu___241_6388.repl_curmod);
              repl_env = env;
              repl_ts = (uu___241_6388.repl_ts);
              repl_stdin = (uu___241_6388.repl_stdin);
              repl_names = (uu___241_6388.repl_names)
            } in
          (results, (FStar_Util.Inl st')) in
        let dummy_let_fragment term1 =
          let dummy_decl =
            FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
          {
            FStar_Parser_ParseIt.frag_text = dummy_decl;
            FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
            FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
          } in
        let normalize_term1 tcenv rules1 t =
          FStar_TypeChecker_Normalize.normalize rules1 tcenv t in
        let find_let_body ses =
          match ses with
          | {
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                ((uu____6428,{ FStar_Syntax_Syntax.lbname = uu____6429;
                               FStar_Syntax_Syntax.lbunivs = uu____6430;
                               FStar_Syntax_Syntax.lbtyp = uu____6431;
                               FStar_Syntax_Syntax.lbeff = uu____6432;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____6434);
              FStar_Syntax_Syntax.sigrng = uu____6435;
              FStar_Syntax_Syntax.sigquals = uu____6436;
              FStar_Syntax_Syntax.sigmeta = uu____6437;
              FStar_Syntax_Syntax.sigattrs = uu____6438;_}::[] ->
              FStar_Pervasives_Native.Some def
          | uu____6467 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____6480 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____6480 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____6504) ->
              FStar_Pervasives_Native.Some decls
          | uu____6549 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____6581 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____6581 in
        let typecheck tcenv decls =
          let uu____6599 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____6599 with | (ses,uu____6613,uu____6614) -> ses in
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None  ->
                 [FStar_TypeChecker_Normalize.Beta;
                 FStar_TypeChecker_Normalize.Iota;
                 FStar_TypeChecker_Normalize.Zeta;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant])
            [FStar_TypeChecker_Normalize.Inlining;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.Primops] in
        run_and_rewind st
          (fun st1  ->
             let uu____6642 = st1.repl_env in
             match uu____6642 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____6654 ->
                      let uu____6655 = parse1 frag in
                      (match uu____6655 with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr "Count not parse this term"))
                       | FStar_Pervasives_Native.Some decls ->
                           (try
                              let decls1 = desugar dsenv decls in
                              let ses = typecheck tcenv decls1 in
                              match find_let_body ses with
                              | FStar_Pervasives_Native.None  ->
                                  (QueryNOK,
                                    (FStar_Util.JsonStr
                                       "Typechecking yielded an unexpected term"))
                              | FStar_Pervasives_Native.Some def ->
                                  let normalized =
                                    normalize_term1 tcenv rules1 def in
                                  let uu____6699 =
                                    let uu____6700 =
                                      term_to_string tcenv normalized in
                                    FStar_Util.JsonStr uu____6700 in
                                  (QueryOK, uu____6699)
                            with
                            | e ->
                                let uu____6710 =
                                  let uu____6711 =
                                    FStar_Errors.issue_of_exn e in
                                  match uu____6711 with
                                  | FStar_Pervasives_Native.Some issue ->
                                      let uu____6715 =
                                        FStar_Errors.format_issue issue in
                                      FStar_Util.JsonStr uu____6715
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Exn.raise e in
                                (QueryNOK, uu____6710)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6737 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6751 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let __proj__Mksearch_term__item__st_negate: search_term -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_negate
let __proj__Mksearch_term__item__st_term: search_term -> search_term' =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_term
let st_cost: search_term' -> Prims.int =
  fun uu___227_6775  ->
    match uu___227_6775 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ:
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref;}
let __proj__Mksearch_candidate__item__sc_lid:
  search_candidate -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_lid
let __proj__Mksearch_candidate__item__sc_typ:
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_typ
let __proj__Mksearch_candidate__item__sc_fvars:
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_fvars
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____6943 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____6950 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____6943; sc_fvars = uu____6950 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____6999 = FStar_ST.op_Bang sc.sc_typ in
      match uu____6999 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____7024 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____7024 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7045,typ),uu____7047) ->
                typ in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____7091 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____7091 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7134 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____7134 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____7177 = sc_typ tcenv sc in term_to_string tcenv uu____7177 in
        let uu____7178 =
          let uu____7185 =
            let uu____7190 =
              let uu____7191 =
                let uu____7192 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____7192.FStar_Ident.str in
              FStar_Util.JsonStr uu____7191 in
            ("lid", uu____7190) in
          [uu____7185; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____7178
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____7212 -> true
    | uu____7213 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____7221 -> uu____7221
let run_search:
  'Auu____7228 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____7228) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____7249 = st.repl_env in
      match uu____7249 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____7277 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____7277 in
            found <> term.st_negate in
          let parse1 search_str1 =
            let parse_one term =
              let negate = FStar_Util.starts_with term "-" in
              let term1 =
                if negate
                then FStar_Util.substring_from term (Prims.parse_int "1")
                else term in
              let beg_quote = FStar_Util.starts_with term1 "\"" in
              let end_quote = FStar_Util.ends_with term1 "\"" in
              let strip_quotes str =
                if (FStar_String.length str) < (Prims.parse_int "2")
                then FStar_Exn.raise (InvalidSearch "Empty search term")
                else
                  FStar_Util.substring str (Prims.parse_int "1")
                    ((FStar_String.length term1) - (Prims.parse_int "2")) in
              let parsed =
                if beg_quote <> end_quote
                then
                  let uu____7301 =
                    let uu____7302 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____7302 in
                  FStar_Exn.raise uu____7301
                else
                  if beg_quote
                  then
                    (let uu____7304 = strip_quotes term1 in
                     NameContainsStr uu____7304)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____7307 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____7307 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____7310 =
                           let uu____7311 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____7311 in
                         FStar_Exn.raise uu____7310
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____7327 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____7327 in
          let results =
            try
              let terms = parse1 search_str in
              let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
              let all_candidates = FStar_List.map sc_of_lid all_lidents in
              let matches_all candidate =
                FStar_List.for_all (st_matches candidate) terms in
              let cmp r1 r2 =
                FStar_Util.compare (r1.sc_lid).FStar_Ident.str
                  (r2.sc_lid).FStar_Ident.str in
              let results = FStar_List.filter matches_all all_candidates in
              let sorted1 = FStar_Util.sort_with cmp results in
              let js =
                FStar_List.map (json_of_search_result dsenv tcenv) sorted1 in
              match results with
              | [] ->
                  let kwds =
                    let uu____7390 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____7390 in
                  let uu____7393 =
                    let uu____7394 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____7394 in
                  FStar_Exn.raise uu____7393
              | uu____7399 -> (QueryOK, (FStar_Util.JsonList js))
            with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
          (results, (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun uu___228_7450  ->
      match uu___228_7450 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c,peek1) -> run_push st kind text1 l c peek1
      | AutoComplete (search_term,kind) ->
          run_autocomplete st search_term kind
      | Lookup (symbol,pos_opt,rqi) -> run_lookup st symbol pos_opt rqi
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
      | MissingCurrentModule  -> run_missing_current_module st (Obj.magic ())
      | ProtocolViolation query -> run_protocol_violation st query
let validate_query: repl_state -> query -> query =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push (SyntaxCheck ,uu____7513,uu____7514,uu____7515,false ) ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____7516 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = MissingCurrentModule; qid = (q.qid) }
           | uu____7517 -> q)
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query =
      let uu____7523 = read_interactive_query st.repl_stdin in
      validate_query st uu____7523 in
    let uu____7524 = let uu____7537 = run_query st in uu____7537 query.qq in
    match uu____7524 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____7581 =
      let uu____7584 = FStar_ST.op_Bang issues in e :: uu____7584 in
    FStar_ST.op_Colon_Equals issues uu____7581 in
  let count_errors uu____7654 =
    let uu____7655 =
      let uu____7658 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____7658 in
    FStar_List.length uu____7655 in
  let report1 uu____7700 =
    let uu____7701 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____7701 in
  let clear1 uu____7739 = FStar_ST.op_Colon_Equals issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  }
let interactive_printer: FStar_Util.printer =
  {
    FStar_Util.printer_prinfo =
      (fun s  -> write_message "info" (FStar_Util.JsonStr s));
    FStar_Util.printer_prwarning =
      (fun s  -> write_message "warning" (FStar_Util.JsonStr s));
    FStar_Util.printer_prerror =
      (fun s  -> write_message "error" (FStar_Util.JsonStr s));
    FStar_Util.printer_prgeneric =
      (fun label1  ->
         fun get_string  ->
           fun get_json  ->
             let uu____7794 = get_json () in write_message label1 uu____7794)
  }
let add_module_completions:
  Prims.string Prims.list ->
    FStar_Interactive_CompletionTable.table ->
      FStar_Interactive_CompletionTable.table
  =
  fun deps  ->
    fun table  ->
      let mods = FStar_Parser_Dep.build_inclusion_candidates_list () in
      let deps_set =
        let uu____7817 = FStar_Util.psmap_empty () in
        FStar_List.fold_left
          (fun acc  ->
             fun dep1  ->
               let uu____7829 = FStar_Parser_Dep.lowercase_module_name dep1 in
               FStar_Util.psmap_add acc uu____7829 true) uu____7817 deps in
      let loaded modname =
        FStar_Util.psmap_find_default deps_set
          (FStar_String.lowercase modname) false in
      FStar_List.fold_left
        (fun table1  ->
           fun uu____7845  ->
             match uu____7845 with
             | (modname,_path) ->
                 let ns_query = FStar_Util.split modname "." in
                 let uu____7855 = loaded modname in
                 FStar_Interactive_CompletionTable.register_module_path
                   table1 uu____7855 ns_query) table mods
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____7861 = deps_of_our_file filename in
     match uu____7861 with
     | (deps,maybe_intf) ->
         let env = FStar_Universal.init_env () in
         let uu____7885 = track_name_changes env in
         (match uu____7885 with
          | (env1,finish_name_tracking) ->
              let env2 = tc_prims env1 in
              let uu____7921 =
                tc_deps FStar_Pervasives_Native.None [] env2 deps [] in
              (match uu____7921 with
               | (stack,env3,ts) ->
                   let initial_range =
                     let uu____7948 =
                       FStar_Range.mk_pos (Prims.parse_int "1")
                         (Prims.parse_int "0") in
                     let uu____7949 =
                       FStar_Range.mk_pos (Prims.parse_int "1")
                         (Prims.parse_int "0") in
                     FStar_Range.mk_range "<input>" uu____7948 uu____7949 in
                   let env4 =
                     let uu____7955 =
                       FStar_TypeChecker_Env.set_range
                         (FStar_Pervasives_Native.snd env3) initial_range in
                     ((FStar_Pervasives_Native.fst env3), uu____7955) in
                   let env5 =
                     match maybe_intf with
                     | FStar_Pervasives_Native.Some intf ->
                         FStar_Universal.load_interface_decls env4 intf
                     | FStar_Pervasives_Native.None  -> env4 in
                   let uu____7966 = finish_name_tracking env5 in
                   (match uu____7966 with
                    | (env6,name_events) ->
                        (FStar_TypeChecker_Env.toggle_id_info
                           (FStar_Pervasives_Native.snd env6) true;
                         (let names1 =
                            add_module_completions deps
                              FStar_Interactive_CompletionTable.empty in
                          let init_st =
                            let uu____7982 = FStar_Util.open_stdin () in
                            let uu____7983 =
                              commit_name_tracking
                                FStar_Pervasives_Native.None names1
                                name_events in
                            {
                              repl_line = (Prims.parse_int "1");
                              repl_column = (Prims.parse_int "0");
                              repl_fname = filename;
                              repl_stack = stack;
                              repl_curmod = FStar_Pervasives_Native.None;
                              repl_env = env6;
                              repl_ts = ts;
                              repl_stdin = uu____7982;
                              repl_names = uu____7983
                            } in
                          let uu____7984 =
                            (FStar_Options.record_hints ()) ||
                              (FStar_Options.use_hints ()) in
                          if uu____7984
                          then
                            let uu____7985 =
                              let uu____7986 = FStar_Options.file_list () in
                              FStar_List.hd uu____7986 in
                            FStar_SMTEncoding_Solver.with_hints_db uu____7985
                              (fun uu____7990  -> go init_st)
                          else go init_st))))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____7999 =
       let uu____8000 = FStar_Options.codegen () in
       FStar_Option.isSome uu____8000 in
     if uu____7999
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e ->
         (FStar_Errors.set_handler FStar_Errors.default_handler;
          FStar_Exn.raise e))