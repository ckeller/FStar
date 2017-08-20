open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize
  :FStar_TypeChecker_Normalize.step Prims.list ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let (bnorm
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun e  -> fun t  -> normalize [] e t
type goal =
  {
  context: env;
  witness: FStar_Syntax_Syntax.term;
  goal_ty: FStar_Syntax_Syntax.typ;
  opts: FStar_Options.optionstate;}
let (__proj__Mkgoal__item__context :goal -> env)=
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__context
let (__proj__Mkgoal__item__witness :goal -> FStar_Syntax_Syntax.term)=
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__witness
let (__proj__Mkgoal__item__goal_ty :goal -> FStar_Syntax_Syntax.typ)=
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__goal_ty
let (__proj__Mkgoal__item__opts :goal -> FStar_Options.optionstate)=
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} -> __fname__opts
type proofstate =
  {
  main_context: env;
  main_goal: goal;
  all_implicits: implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;}
let (__proj__Mkproofstate__item__main_context :proofstate -> env)=
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_context
let (__proj__Mkproofstate__item__main_goal :proofstate -> goal)=
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_goal
let (__proj__Mkproofstate__item__all_implicits :proofstate -> implicits)=
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__all_implicits
let (__proj__Mkproofstate__item__goals :proofstate -> goal Prims.list)=
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__goals
let (__proj__Mkproofstate__item__smt_goals :proofstate -> goal Prims.list)=
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__smt_goals
type 'a result =
  | Success of ('a,proofstate) FStar_Pervasives_Native.tuple2
  | Failed of (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
let uu___is_Success : 'a . 'a result -> Prims.bool=
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____211 -> false
let __proj__Success__item___0 :
  'a . 'a result -> ('a,proofstate) FStar_Pervasives_Native.tuple2=
  fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed : 'a . 'a result -> Prims.bool=
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____257 -> false
let __proj__Failed__item___0 :
  'a . 'a result -> (Prims.string,proofstate) FStar_Pervasives_Native.tuple2=
  fun projectee  -> match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let (uu___is_TacFailure :Prims.exn -> Prims.bool)=
  fun projectee  ->
    match projectee with | TacFailure uu____292 -> true | uu____293 -> false
let (__proj__TacFailure__item__uu___ :Prims.exn -> Prims.string)=
  fun projectee  -> match projectee with | TacFailure uu____301 -> uu____301
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let __proj__Mktac__item__tac_f : 'a . 'a tac -> proofstate -> 'a result=
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
let mk_tac : 'a . (proofstate -> 'a result) -> 'a tac=
  fun f  -> { tac_f = f }
let run : 'Auu____365 . 'Auu____365 tac -> proofstate -> 'Auu____365 result=
  fun t  -> fun p  -> t.tac_f p
let ret : 'a . 'a -> 'a tac= fun x  -> mk_tac (fun p  -> Success (x, p))
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac=
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____432 = run t1 p in
           match uu____432 with
           | Success (a,q) -> let uu____439 = t2 a in run uu____439 q
           | Failed (msg,q) -> Failed (msg, q))
let (idtac :Prims.unit tac)= ret ()
let (goal_to_string :goal -> Prims.string)=
  fun g  ->
    let g_binders =
      let uu____451 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____451
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____452 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____453 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____452 uu____453
let (tacprint :Prims.string -> Prims.unit)=
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 :Prims.string -> Prims.string -> Prims.unit)=
  fun s  ->
    fun x  ->
      let uu____466 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____466
let (tacprint2 :Prims.string -> Prims.string -> Prims.string -> Prims.unit)=
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____479 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____479
let (tacprint3
  :Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit)=
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____496 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____496
let (comp_to_typ :FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ)=
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____502) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____512) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let (is_irrelevant :goal -> Prims.bool)=
  fun g  ->
    let uu____526 =
      let uu____531 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____531 in
    match uu____526 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____537 -> false
let dump_goal : 'Auu____548 . 'Auu____548 -> goal -> Prims.unit=
  fun ps  ->
    fun goal  -> let uu____558 = goal_to_string goal in tacprint uu____558
let (dump_cur :proofstate -> Prims.string -> Prims.unit)=
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____568 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____572 = FStar_List.hd ps.goals in dump_goal ps uu____572))
let (ps_to_string
  :(Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> Prims.string)=
  fun uu____580  ->
    match uu____580 with
    | (msg,ps) ->
        let uu____587 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
        let uu____588 =
          let uu____589 = FStar_List.map goal_to_string ps.goals in
          FStar_String.concat "\n" uu____589 in
        let uu____592 =
          FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
        let uu____593 =
          let uu____594 = FStar_List.map goal_to_string ps.smt_goals in
          FStar_String.concat "\n" uu____594 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____587 uu____588 uu____592 uu____593
let (goal_to_json :goal -> FStar_Util.json)=
  fun g  ->
    let g_binders =
      let uu____602 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____602 FStar_Syntax_Print.binders_to_json in
    let uu____603 =
      let uu____610 =
        let uu____617 =
          let uu____622 =
            let uu____623 =
              let uu____630 =
                let uu____635 =
                  let uu____636 = FStar_Syntax_Print.term_to_string g.witness in
                  FStar_Util.JsonStr uu____636 in
                ("witness", uu____635) in
              let uu____637 =
                let uu____644 =
                  let uu____649 =
                    let uu____650 =
                      FStar_Syntax_Print.term_to_string g.goal_ty in
                    FStar_Util.JsonStr uu____650 in
                  ("type", uu____649) in
                [uu____644] in
              uu____630 :: uu____637 in
            FStar_Util.JsonAssoc uu____623 in
          ("goal", uu____622) in
        [uu____617] in
      ("hyps", g_binders) :: uu____610 in
    FStar_Util.JsonAssoc uu____603
let (ps_to_json
  :(Prims.string,proofstate) FStar_Pervasives_Native.tuple2 ->
     FStar_Util.json)=
  fun uu____682  ->
    match uu____682 with
    | (msg,ps) ->
        let uu____689 =
          let uu____696 =
            let uu____703 =
              let uu____708 =
                let uu____709 = FStar_List.map goal_to_json ps.goals in
                FStar_Util.JsonList uu____709 in
              ("goals", uu____708) in
            let uu____712 =
              let uu____719 =
                let uu____724 =
                  let uu____725 = FStar_List.map goal_to_json ps.smt_goals in
                  FStar_Util.JsonList uu____725 in
                ("smt-goals", uu____724) in
              [uu____719] in
            uu____703 :: uu____712 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____696 in
        FStar_Util.JsonAssoc uu____689
let (dump_proofstate :proofstate -> Prims.string -> Prims.unit)=
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____754  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
let (print_proof_state1 :Prims.string -> Prims.unit tac)=
  fun msg  -> mk_tac (fun p  -> dump_cur p msg; Success ((), p))
let (print_proof_state :Prims.string -> Prims.unit tac)=
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let (get :proofstate tac)= mk_tac (fun p  -> Success (p, p))
let (tac_verb_dbg :Prims.bool FStar_Pervasives_Native.option FStar_ST.ref)=
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec (log :proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit)=
  fun ps  ->
    fun f  ->
      let uu____814 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____814 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____836 =
              let uu____839 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____839 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____836);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let (mlog :(Prims.unit -> Prims.unit) -> Prims.unit tac)=
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail : 'Auu____879 . Prims.string -> 'Auu____879 tac=
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____890 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail") in
          if uu____890
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
let fail1 : 'Auu____898 . Prims.string -> Prims.string -> 'Auu____898 tac=
  fun msg  ->
    fun x  -> let uu____909 = FStar_Util.format1 msg x in fail uu____909
let fail2 :
  'Auu____918 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____918 tac=
  fun msg  ->
    fun x  ->
      fun y  -> let uu____933 = FStar_Util.format2 msg x y in fail uu____933
let fail3 :
  'Auu____944 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____944 tac=
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____963 = FStar_Util.format3 msg x y z in fail uu____963
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac=
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____991 = run t ps in
         match uu____991 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____1005,uu____1006) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
let (set :proofstate -> Prims.unit tac)=
  fun p  -> mk_tac (fun uu____1021  -> Success ((), p))
let (solve :goal -> FStar_Syntax_Syntax.typ -> Prims.unit)=
  fun goal  ->
    fun solution  ->
      let uu____1030 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____1030
      then ()
      else
        (let uu____1032 =
           let uu____1033 =
             let uu____1034 = FStar_Syntax_Print.term_to_string solution in
             let uu____1035 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____1036 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1034
               uu____1035 uu____1036 in
           TacFailure uu____1033 in
         FStar_Exn.raise uu____1032)
let (dismiss :Prims.unit tac)=
  bind get
    (fun p  ->
       let uu____1042 =
         let uu___86_1043 = p in
         let uu____1044 = FStar_List.tl p.goals in
         {
           main_context = (uu___86_1043.main_context);
           main_goal = (uu___86_1043.main_goal);
           all_implicits = (uu___86_1043.all_implicits);
           goals = uu____1044;
           smt_goals = (uu___86_1043.smt_goals)
         } in
       set uu____1042)
let (dismiss_all :Prims.unit tac)=
  bind get
    (fun p  ->
       set
         (let uu___87_1053 = p in
          {
            main_context = (uu___87_1053.main_context);
            main_goal = (uu___87_1053.main_goal);
            all_implicits = (uu___87_1053.all_implicits);
            goals = [];
            smt_goals = (uu___87_1053.smt_goals)
          }))
let (add_goals :goal Prims.list -> Prims.unit tac)=
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___88_1070 = p in
            {
              main_context = (uu___88_1070.main_context);
              main_goal = (uu___88_1070.main_goal);
              all_implicits = (uu___88_1070.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___88_1070.smt_goals)
            }))
let (add_smt_goals :goal Prims.list -> Prims.unit tac)=
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___89_1087 = p in
            {
              main_context = (uu___89_1087.main_context);
              main_goal = (uu___89_1087.main_goal);
              all_implicits = (uu___89_1087.all_implicits);
              goals = (uu___89_1087.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let (push_goals :goal Prims.list -> Prims.unit tac)=
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1104 = p in
            {
              main_context = (uu___90_1104.main_context);
              main_goal = (uu___90_1104.main_goal);
              all_implicits = (uu___90_1104.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___90_1104.smt_goals)
            }))
let (push_smt_goals :goal Prims.list -> Prims.unit tac)=
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1121 = p in
            {
              main_context = (uu___91_1121.main_context);
              main_goal = (uu___91_1121.main_goal);
              all_implicits = (uu___91_1121.all_implicits);
              goals = (uu___91_1121.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let (replace_cur :goal -> Prims.unit tac)=
  fun g  -> bind dismiss (fun uu____1131  -> add_goals [g])
let (add_implicits :implicits -> Prims.unit tac)=
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1144 = p in
            {
              main_context = (uu___92_1144.main_context);
              main_goal = (uu___92_1144.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___92_1144.goals);
              smt_goals = (uu___92_1144.smt_goals)
            }))
let (new_uvar
  :env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)=
  fun env  ->
    fun typ  ->
      let uu____1169 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1169 with
      | (u,uu____1185,g_u) ->
          let uu____1199 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1199 (fun uu____1203  -> ret u)
let (is_true :FStar_Syntax_Syntax.term -> Prims.bool)=
  fun t  ->
    let uu____1208 = FStar_Syntax_Util.un_squash t in
    match uu____1208 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1218 =
          let uu____1219 = FStar_Syntax_Subst.compress t' in
          uu____1219.FStar_Syntax_Syntax.n in
        (match uu____1218 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1223 -> false)
    | uu____1224 -> false
let (is_false :FStar_Syntax_Syntax.term -> Prims.bool)=
  fun t  ->
    let uu____1233 = FStar_Syntax_Util.un_squash t in
    match uu____1233 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1243 =
          let uu____1244 = FStar_Syntax_Subst.compress t' in
          uu____1244.FStar_Syntax_Syntax.n in
        (match uu____1243 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1248 -> false)
    | uu____1249 -> false
let (cur_goal :goal tac)=
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let (add_irrelevant_goal
  :env ->
     FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)=
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi in
        let uu____1283 = new_uvar env typ in
        bind uu____1283
          (fun u  ->
             let goal = { context = env; witness = u; goal_ty = typ; opts } in
             add_goals [goal])
let (smt :Prims.unit tac)=
  bind cur_goal
    (fun g  ->
       let uu____1295 = is_irrelevant g in
       if uu____1295
       then bind dismiss (fun uu____1299  -> add_smt_goals [g])
       else
         (let uu____1301 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1301))
let divide :
  'a 'b .
    Prims.int ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac=
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____1347 =
               try
                 let uu____1381 = FStar_List.splitAt n1 p.goals in
                 ret uu____1381
               with | uu____1411 -> fail "divide: not enough goals" in
             bind uu____1347
               (fun uu____1438  ->
                  match uu____1438 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___93_1464 = p in
                        {
                          main_context = (uu___93_1464.main_context);
                          main_goal = (uu___93_1464.main_goal);
                          all_implicits = (uu___93_1464.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___94_1466 = p in
                        {
                          main_context = (uu___94_1466.main_context);
                          main_goal = (uu___94_1466.main_goal);
                          all_implicits = (uu___94_1466.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1467 = set lp in
                      bind uu____1467
                        (fun uu____1475  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1489 = set rp in
                                     bind uu____1489
                                       (fun uu____1497  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___95_1513 = p in
                                                      {
                                                        main_context =
                                                          (uu___95_1513.main_context);
                                                        main_goal =
                                                          (uu___95_1513.main_goal);
                                                        all_implicits =
                                                          (uu___95_1513.all_implicits);
                                                        goals =
                                                          (FStar_List.append
                                                             lp'.goals
                                                             rp'.goals);
                                                        smt_goals =
                                                          (FStar_List.append
                                                             lp'.smt_goals
                                                             (FStar_List.append
                                                                rp'.smt_goals
                                                                p.smt_goals))
                                                      } in
                                                    let uu____1514 = set p' in
                                                    bind uu____1514
                                                      (fun uu____1522  ->
                                                         ret (a, b))))))))))
let focus : 'a . 'a tac -> 'a tac=
  fun f  ->
    let uu____1542 = divide (Prims.parse_int "1") f idtac in
    bind uu____1542
      (fun uu____1555  -> match uu____1555 with | (a,()) -> ret a)
let rec map : 'a . 'a tac -> 'a Prims.list tac=
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1591::uu____1592 ->
             let uu____1595 =
               let uu____1604 = map tau in
               divide (Prims.parse_int "1") tau uu____1604 in
             bind uu____1595
               (fun uu____1622  ->
                  match uu____1622 with | (h,t) -> ret (h :: t)))
let (seq :Prims.unit tac -> Prims.unit tac -> Prims.unit tac)=
  fun t1  ->
    fun t2  ->
      let uu____1661 =
        bind t1
          (fun uu____1666  ->
             let uu____1667 = map t2 in
             bind uu____1667 (fun uu____1675  -> ret ())) in
      focus uu____1661
let (intro
  :(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
     FStar_Pervasives_Native.tuple2 tac)=
  bind cur_goal
    (fun goal  ->
       let uu____1698 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1698 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1717 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1717 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1752 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1757 =
                  let uu____1758 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1758 in
                if uu____1757
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1780 = new_uvar env' typ' in
                   bind uu____1780
                     (fun u  ->
                        let uu____1791 =
                          let uu____1792 =
                            FStar_Syntax_Util.abs [b1] u
                              FStar_Pervasives_Native.None in
                          FStar_TypeChecker_Rel.teq_nosmt goal.context
                            goal.witness uu____1792 in
                        if uu____1791
                        then
                          let uu____1807 =
                            let uu____1810 =
                              let uu___98_1811 = goal in
                              let uu____1812 = bnorm env' u in
                              let uu____1813 = bnorm env' typ' in
                              {
                                context = env';
                                witness = uu____1812;
                                goal_ty = uu____1813;
                                opts = (uu___98_1811.opts)
                              } in
                            replace_cur uu____1810 in
                          bind uu____1807 (fun uu____1819  -> ret b1)
                        else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1833 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1833)
let (intro_rec
  :(FStar_Syntax_Syntax.binder,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                 FStar_Pervasives_Native.tuple2)
     FStar_Pervasives_Native.tuple2 tac)=
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____1870 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1870 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1893 = FStar_Syntax_Subst.open_comp [b] c in
            (match uu____1893 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1932 ->
                       failwith
                         "impossible: open_comp returned different amount of binders" in
                 let uu____1937 =
                   let uu____1938 = FStar_Syntax_Util.is_total_comp c1 in
                   Prims.op_Negation uu____1938 in
                 if uu____1937
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty in
                    let bs1 =
                      let uu____1962 = FStar_Syntax_Syntax.mk_binder bv in
                      [uu____1962; b1] in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1 in
                    let uu____1972 =
                      let uu____1975 = comp_to_typ c1 in
                      new_uvar env' uu____1975 in
                    bind uu____1972
                      (fun u  ->
                         let lb =
                           let uu____1996 =
                             FStar_Syntax_Util.abs [b1] u
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Util.mk_letbinding
                             (FStar_Util.Inl bv) [] goal.goal_ty
                             FStar_Parser_Const.effect_Tot_lid uu____1996 in
                         let body = FStar_Syntax_Syntax.bv_to_name bv in
                         let uu____2008 =
                           FStar_Syntax_Subst.close_let_rec [lb] body in
                         match uu____2008 with
                         | (lbs,body1) ->
                             let tm =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((true, lbs), body1))
                                 FStar_Pervasives_Native.None
                                 (goal.witness).FStar_Syntax_Syntax.pos in
                             (FStar_Util.print_string "calling teq_nosmt\n";
                              (let res =
                                 FStar_TypeChecker_Rel.teq_nosmt goal.context
                                   goal.witness tm in
                               if res
                               then
                                 let uu____2054 =
                                   let uu____2057 =
                                     let uu___99_2058 = goal in
                                     let uu____2059 = bnorm env' u in
                                     let uu____2060 =
                                       let uu____2061 = comp_to_typ c1 in
                                       bnorm env' uu____2061 in
                                     {
                                       context = env';
                                       witness = uu____2059;
                                       goal_ty = uu____2060;
                                       opts = (uu___99_2058.opts)
                                     } in
                                   replace_cur uu____2057 in
                                 bind uu____2054
                                   (fun uu____2072  ->
                                      let uu____2073 =
                                        let uu____2082 =
                                          FStar_Syntax_Syntax.mk_binder bv in
                                        (uu____2082, b1) in
                                      ret uu____2073)
                               else fail "intro_rec: unification failed")))))
        | FStar_Pervasives_Native.None  ->
            let uu____2108 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2108))
let (norm :FStar_Reflection_Data.norm_step Prims.list -> Prims.unit tac)=
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let tr s1 =
           match s1 with
           | FStar_Reflection_Data.Simpl  ->
               [FStar_TypeChecker_Normalize.Simplify]
           | FStar_Reflection_Data.WHNF  ->
               [FStar_TypeChecker_Normalize.WHNF]
           | FStar_Reflection_Data.Primops  ->
               [FStar_TypeChecker_Normalize.Primops]
           | FStar_Reflection_Data.Delta  ->
               [FStar_TypeChecker_Normalize.UnfoldUntil
                  FStar_Syntax_Syntax.Delta_constant]
           | FStar_Reflection_Data.UnfoldOnly l ->
               let uu____2146 =
                 let uu____2147 =
                   FStar_List.map FStar_Syntax_Syntax.lid_of_fv l in
                 FStar_TypeChecker_Normalize.UnfoldOnly uu____2147 in
               [uu____2146] in
         let steps =
           let uu____2153 =
             let uu____2156 = FStar_List.map tr s in
             FStar_List.flatten uu____2156 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2153 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___100_2167 = goal in
            {
              context = (uu___100_2167.context);
              witness = w;
              goal_ty = t;
              opts = (uu___100_2167.opts)
            }))
let (istrivial :env -> FStar_Syntax_Syntax.term -> Prims.bool)=
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t1 = normalize steps e t in is_true t1
let (trivial :Prims.unit tac)=
  bind cur_goal
    (fun goal  ->
       let uu____2186 = istrivial goal.context goal.goal_ty in
       if uu____2186
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____2191 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____2191))
let (exact :FStar_Syntax_Syntax.term -> Prims.unit tac)=
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2203 =
           try
             let uu____2231 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2231
           with
           | e ->
               let uu____2258 = FStar_Syntax_Print.term_to_string t in
               let uu____2259 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2258
                 uu____2259 in
         bind uu____2203
           (fun uu____2277  ->
              match uu____2277 with
              | (t1,typ,guard) ->
                  let uu____2289 =
                    let uu____2290 =
                      let uu____2291 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2291 in
                    Prims.op_Negation uu____2290 in
                  if uu____2289
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2295 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2295
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2300 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2301 =
                          let uu____2302 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2302 in
                        let uu____2303 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2300 uu____2301 uu____2303))))
let (exact_lemma :FStar_Syntax_Syntax.term -> Prims.unit tac)=
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2315 =
           try
             let uu____2343 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2343
           with
           | e ->
               let uu____2370 = FStar_Syntax_Print.term_to_string t in
               let uu____2371 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2370
                 uu____2371 in
         bind uu____2315
           (fun uu____2389  ->
              match uu____2389 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2407 =
                       let uu____2408 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2408 in
                     if uu____2407
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2412 =
                          let uu____2421 =
                            let uu____2430 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2430.FStar_Syntax_Syntax.effect_args in
                          match uu____2421 with
                          | pre::post::uu____2441 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2482 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2412 with
                        | (pre,post) ->
                            let uu____2511 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2511
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2516  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2518 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2519 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2520 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2518 uu____2519 uu____2520)))))
let (uvar_free_in_goal :FStar_Syntax_Syntax.uvar -> goal -> Prims.bool)=
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2532 =
          let uu____2539 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____2539 in
        FStar_List.map FStar_Pervasives_Native.fst uu____2532 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let (uvar_free :FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool)=
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec (__apply :Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)=
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2577 = let uu____2582 = exact tm in trytac uu____2582 in
           bind uu____2577
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____2595 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____2595 with
                     | (tm1,typ,guard) ->
                         let uu____2607 =
                           let uu____2608 =
                             let uu____2609 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____2609 in
                           Prims.op_Negation uu____2608 in
                         if uu____2607
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____2613 = FStar_Syntax_Util.arrow_one typ in
                            match uu____2613 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2626 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____2626
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____2642 =
                                  let uu____2643 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2643 in
                                if uu____2642
                                then fail "apply: not total"
                                else
                                  (let uu____2647 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2647
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm1
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.context).FStar_TypeChecker_Env.range in
                                        let uu____2665 = __apply uopt tm' in
                                        bind uu____2665
                                          (fun uu____2672  ->
                                             let uu____2673 =
                                               let uu____2674 =
                                                 let uu____2677 =
                                                   let uu____2678 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2678 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2677 in
                                               uu____2674.FStar_Syntax_Syntax.n in
                                             match uu____2673 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2706) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2734 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2734
                                                      then ret ()
                                                      else
                                                        (let uu____2738 =
                                                           let uu____2741 =
                                                             let uu____2742 =
                                                               bnorm
                                                                 goal.context
                                                                 u in
                                                             let uu____2743 =
                                                               bnorm
                                                                 goal.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               context =
                                                                 (goal.context);
                                                               witness =
                                                                 uu____2742;
                                                               goal_ty =
                                                                 uu____2743;
                                                               opts =
                                                                 (goal.opts)
                                                             } in
                                                           [uu____2741] in
                                                         add_goals uu____2738))
                                             | uu____2744 -> ret ())))))))
let (apply :FStar_Syntax_Syntax.term -> Prims.unit tac)=
  fun tm  -> let uu____2753 = __apply true tm in focus uu____2753
let (apply_lemma :FStar_Syntax_Syntax.term -> Prims.unit tac)=
  fun tm  ->
    let is_unit_t t =
      let uu____2768 =
        let uu____2769 = FStar_Syntax_Subst.compress t in
        uu____2769.FStar_Syntax_Syntax.n in
      match uu____2768 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          true
      | uu____2773 -> false in
    bind cur_goal
      (fun goal  ->
         let uu____2781 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____2781 with
         | (tm1,t,guard) ->
             let uu____2793 =
               let uu____2794 =
                 let uu____2795 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2795 in
               Prims.op_Negation uu____2794 in
             if uu____2793
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2799 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2799 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2829 =
                         FStar_List.fold_left
                           (fun uu____2875  ->
                              fun uu____2876  ->
                                match (uu____2875, uu____2876) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2979 = is_unit_t b_t in
                                    if uu____2979
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____3017 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____3017 with
                                       | (u,uu____3047,g_u) ->
                                           let uu____3061 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____3061,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2829 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3131 =
                             let uu____3140 =
                               let uu____3149 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3149.FStar_Syntax_Syntax.effect_args in
                             match uu____3140 with
                             | pre::post::uu____3160 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3201 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3131 with
                            | (pre,post) ->
                                let uu____3230 =
                                  let uu____3233 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3233 goal.goal_ty in
                                (match uu____3230 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3236 =
                                       let uu____3237 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3237 in
                                     let uu____3238 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3236 uu____3238
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____3240 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         goal.context g in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____3311  ->
                                               match uu____3311 with
                                               | (uu____3324,uu____3325,uu____3326,tm2,uu____3328,uu____3329)
                                                   ->
                                                   let uu____3330 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3330 with
                                                    | (hd1,uu____3346) ->
                                                        let uu____3367 =
                                                          let uu____3368 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3368.FStar_Syntax_Syntax.n in
                                                        (match uu____3367
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3371 ->
                                                             true
                                                         | uu____3388 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let uu____3390 =
                                         add_implicits implicits1 in
                                       bind uu____3390
                                         (fun uu____3394  ->
                                            bind dismiss
                                              (fun uu____3403  ->
                                                 let is_free_uvar uv t1 =
                                                   let free_uvars =
                                                     let uu____3414 =
                                                       let uu____3421 =
                                                         FStar_Syntax_Free.uvars
                                                           t1 in
                                                       FStar_Util.set_elements
                                                         uu____3421 in
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       uu____3414 in
                                                   FStar_List.existsML
                                                     (fun u  ->
                                                        FStar_Syntax_Unionfind.equiv
                                                          u uv) free_uvars in
                                                 let appears uv goals =
                                                   FStar_List.existsML
                                                     (fun g'  ->
                                                        is_free_uvar uv
                                                          g'.goal_ty) goals in
                                                 let checkone t1 goals =
                                                   let uu____3462 =
                                                     FStar_Syntax_Util.head_and_args
                                                       t1 in
                                                   match uu____3462 with
                                                   | (hd1,uu____3478) ->
                                                       (match hd1.FStar_Syntax_Syntax.n
                                                        with
                                                        | FStar_Syntax_Syntax.Tm_uvar
                                                            (uv,uu____3500)
                                                            ->
                                                            appears uv goals
                                                        | uu____3525 -> false) in
                                                 let sub_goals =
                                                   FStar_All.pipe_right
                                                     implicits1
                                                     (FStar_List.map
                                                        (fun uu____3566  ->
                                                           match uu____3566
                                                           with
                                                           | (_msg,_env,_uvar,term,typ,uu____3584)
                                                               ->
                                                               let uu____3585
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   term in
                                                               let uu____3586
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   typ in
                                                               {
                                                                 context =
                                                                   (goal.context);
                                                                 witness =
                                                                   uu____3585;
                                                                 goal_ty =
                                                                   uu____3586;
                                                                 opts =
                                                                   (goal.opts)
                                                               })) in
                                                 let rec filter' f xs =
                                                   match xs with
                                                   | [] -> []
                                                   | x::xs1 ->
                                                       let uu____3624 =
                                                         f x xs1 in
                                                       if uu____3624
                                                       then
                                                         let uu____3627 =
                                                           filter' f xs1 in
                                                         x :: uu____3627
                                                       else filter' f xs1 in
                                                 let sub_goals1 =
                                                   filter'
                                                     (fun g1  ->
                                                        fun goals  ->
                                                          let uu____3641 =
                                                            checkone
                                                              g1.witness
                                                              goals in
                                                          Prims.op_Negation
                                                            uu____3641)
                                                     sub_goals in
                                                 let uu____3642 =
                                                   add_irrelevant_goal
                                                     goal.context pre
                                                     goal.opts in
                                                 bind uu____3642
                                                   (fun uu____3647  ->
                                                      let uu____3648 =
                                                        trytac trivial in
                                                      bind uu____3648
                                                        (fun uu____3656  ->
                                                           add_goals
                                                             sub_goals1)))))))))))
let (destruct_eq'
  :FStar_Syntax_Syntax.typ ->
     (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)=
  fun typ  ->
    let uu____3675 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3675 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3685::(e1,uu____3687)::(e2,uu____3689)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3748 -> FStar_Pervasives_Native.None
let (destruct_eq
  :FStar_Syntax_Syntax.typ ->
     (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)=
  fun typ  ->
    let uu____3771 = destruct_eq' typ in
    match uu____3771 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3801 = FStar_Syntax_Util.un_squash typ in
        (match uu____3801 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let (rewrite :FStar_Syntax_Syntax.binder -> Prims.unit tac)=
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3834 =
           FStar_All.pipe_left mlog
             (fun uu____3844  ->
                let uu____3845 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3846 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3845
                  uu____3846) in
         bind uu____3834
           (fun uu____3854  ->
              let uu____3855 =
                let uu____3862 =
                  let uu____3863 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3863 in
                destruct_eq uu____3862 in
              match uu____3855 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3880 =
                    let uu____3881 = FStar_Syntax_Subst.compress x in
                    uu____3881.FStar_Syntax_Syntax.n in
                  (match uu____3880 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___105_3888 = goal in
                         let uu____3889 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3890 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___105_3888.context);
                           witness = uu____3889;
                           goal_ty = uu____3890;
                           opts = (uu___105_3888.opts)
                         } in
                       replace_cur goal1
                   | uu____3891 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3892 -> fail "Not an equality hypothesis"))
let (clear :Prims.unit tac)=
  bind cur_goal
    (fun goal  ->
       let uu____3904 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3904 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____3926 = FStar_Util.set_mem x fns_ty in
           if uu____3926
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3930 = new_uvar env' goal.goal_ty in
              bind uu____3930
                (fun u  ->
                   let uu____3936 =
                     let uu____3937 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context
                         goal.witness u in
                     Prims.op_Negation uu____3937 in
                   if uu____3936
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___106_3942 = goal in
                        let uu____3943 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____3943;
                          goal_ty = (uu___106_3942.goal_ty);
                          opts = (uu___106_3942.opts)
                        } in
                      bind dismiss (fun uu____3945  -> add_goals [new_goal])))))
let (clear_hd :name -> Prims.unit tac)=
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3957 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3957 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let (revert :Prims.unit tac)=
  bind cur_goal
    (fun goal  ->
       let uu____3984 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3984 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4006 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4006 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___107_4040 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___107_4040.opts)
              }))
let (revert_hd :name -> Prims.unit tac)=
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4052 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4052 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4073 = FStar_Syntax_Print.bv_to_string x in
               let uu____4074 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4073 uu____4074
             else revert)
let rec (revert_all_hd :name Prims.list -> Prims.unit tac)=
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____4092 = revert_all_hd xs1 in
        bind uu____4092 (fun uu____4096  -> revert_hd x)
let (prune :Prims.string -> Prims.unit tac)=
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___108_4113 = g in
           {
             context = ctx';
             witness = (uu___108_4113.witness);
             goal_ty = (uu___108_4113.goal_ty);
             opts = (uu___108_4113.opts)
           } in
         bind dismiss (fun uu____4115  -> add_goals [g']))
let (addns :Prims.string -> Prims.unit tac)=
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___109_4132 = g in
           {
             context = ctx';
             witness = (uu___109_4132.witness);
             goal_ty = (uu___109_4132.goal_ty);
             opts = (uu___109_4132.opts)
           } in
         bind dismiss (fun uu____4134  -> add_goals [g']))
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac=
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4178 = f x in
          bind uu____4178
            (fun y  ->
               let uu____4186 = mapM f xs in
               bind uu____4186 (fun ys  -> ret (y :: ys)))
let rec (tac_bottom_fold_env
  :(env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
     env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)=
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4232 = FStar_Syntax_Subst.compress t in
          uu____4232.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4267 = ff hd1 in
              bind uu____4267
                (fun hd2  ->
                   let fa uu____4287 =
                     match uu____4287 with
                     | (a,q) ->
                         let uu____4300 = ff a in
                         bind uu____4300 (fun a1  -> ret (a1, q)) in
                   let uu____4313 = mapM fa args in
                   bind uu____4313
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4373 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4373 with
               | (bs1,t') ->
                   let uu____4382 =
                     let uu____4385 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4385 t' in
                   bind uu____4382
                     (fun t''  ->
                        let uu____4389 =
                          let uu____4390 =
                            let uu____4407 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4408 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4407, uu____4408, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4390 in
                        ret uu____4389))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4429 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___110_4433 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___110_4433.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___110_4433.FStar_Syntax_Syntax.vars)
                }))
let (pointwise_rec
  :proofstate ->
     Prims.unit tac ->
       FStar_Options.optionstate ->
         FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)=
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____4462 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4462 with
            | (t1,lcomp,g) ->
                let uu____4474 =
                  (let uu____4477 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4477) ||
                    (let uu____4479 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4479) in
                if uu____4474
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4486 = new_uvar env typ in
                   bind uu____4486
                     (fun ut  ->
                        log ps
                          (fun uu____4497  ->
                             let uu____4498 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4499 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4498 uu____4499);
                        (let uu____4500 =
                           let uu____4503 =
                             let uu____4504 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4504 typ t1 ut in
                           add_irrelevant_goal env uu____4503 opts in
                         bind uu____4500
                           (fun uu____4507  ->
                              let uu____4508 =
                                bind tau
                                  (fun uu____4513  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4508))))
let (pointwise :Prims.unit tac -> Prims.unit tac)=
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4534 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4534 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4571  ->
                   let uu____4572 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4572);
              bind dismiss_all
                (fun uu____4575  ->
                   let uu____4576 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4576
                     (fun gt'  ->
                        log ps
                          (fun uu____4586  ->
                             let uu____4587 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4587);
                        (let uu____4588 = push_goals gs in
                         bind uu____4588
                           (fun uu____4592  ->
                              add_goals
                                [(let uu___111_4594 = g in
                                  {
                                    context = (uu___111_4594.context);
                                    witness = (uu___111_4594.witness);
                                    goal_ty = gt';
                                    opts = (uu___111_4594.opts)
                                  })]))))))
let (trefl :Prims.unit tac)=
  bind cur_goal
    (fun g  ->
       let uu____4614 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4614 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4626 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4626 with
            | (hd1,args) ->
                let uu____4659 =
                  let uu____4672 =
                    let uu____4673 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4673.FStar_Syntax_Syntax.n in
                  (uu____4672, args) in
                (match uu____4659 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4687::(l,uu____4689)::(r,uu____4691)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4738 =
                       let uu____4739 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4739 in
                     if uu____4738
                     then
                       let uu____4742 = FStar_Syntax_Print.term_to_string l in
                       let uu____4743 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4742 uu____4743
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4747) ->
                     let uu____4764 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4764))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let (dup :Prims.unit tac)=
  bind cur_goal
    (fun g  ->
       let uu____4772 = new_uvar g.context g.goal_ty in
       bind uu____4772
         (fun u  ->
            let g' =
              let uu___112_4779 = g in
              {
                context = (uu___112_4779.context);
                witness = u;
                goal_ty = (uu___112_4779.goal_ty);
                opts = (uu___112_4779.opts)
              } in
            bind dismiss
              (fun uu____4782  ->
                 let uu____4783 =
                   let uu____4786 =
                     let uu____4787 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4787 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____4786 g.opts in
                 bind uu____4783
                   (fun uu____4790  ->
                      let uu____4791 = add_goals [g'] in
                      bind uu____4791 (fun uu____4795  -> ret ())))))
let (flip :Prims.unit tac)=
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___113_4812 = ps in
              {
                main_context = (uu___113_4812.main_context);
                main_goal = (uu___113_4812.main_goal);
                all_implicits = (uu___113_4812.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___113_4812.smt_goals)
              })
       | uu____4813 -> fail "flip: less than 2 goals")
let (later :Prims.unit tac)=
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___114_4828 = ps in
              {
                main_context = (uu___114_4828.main_context);
                main_goal = (uu___114_4828.main_goal);
                all_implicits = (uu___114_4828.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___114_4828.smt_goals)
              }))
let (qed :Prims.unit tac)=
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4835 -> fail "Not done!")
let (cases
  :FStar_Syntax_Syntax.term ->
     (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2 tac)=
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4877 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4877 with
         | (t1,typ,guard) ->
             let uu____4893 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4893 with
              | (hd1,args) ->
                  let uu____4936 =
                    let uu____4949 =
                      let uu____4950 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4950.FStar_Syntax_Syntax.n in
                    (uu____4949, args) in
                  (match uu____4936 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4969)::(q,uu____4971)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.or_lid
                       ->
                       let v_p =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None p in
                       let v_q =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None q in
                       let g1 =
                         let uu___115_5009 = g in
                         let uu____5010 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5010;
                           witness = (uu___115_5009.witness);
                           goal_ty = (uu___115_5009.goal_ty);
                           opts = (uu___115_5009.opts)
                         } in
                       let g2 =
                         let uu___116_5012 = g in
                         let uu____5013 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5013;
                           witness = (uu___116_5012.witness);
                           goal_ty = (uu___116_5012.goal_ty);
                           opts = (uu___116_5012.opts)
                         } in
                       bind dismiss
                         (fun uu____5020  ->
                            let uu____5021 = add_goals [g1; g2] in
                            bind uu____5021
                              (fun uu____5030  ->
                                 let uu____5031 =
                                   let uu____5036 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5037 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5036, uu____5037) in
                                 ret uu____5031))
                   | uu____5042 ->
                       let uu____5055 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____5055)))
let (set_options :Prims.string -> Prims.unit tac)=
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5078 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5078);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___117_5085 = g in
                 {
                   context = (uu___117_5085.context);
                   witness = (uu___117_5085.witness);
                   goal_ty = (uu___117_5085.goal_ty);
                   opts = opts'
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
let (cur_env :env tac)=
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.context)
let (cur_goal' :FStar_Syntax_Syntax.typ tac)=
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.goal_ty)
let (cur_witness :FStar_Syntax_Syntax.term tac)=
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.witness)
let (unquote
  :FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)=
  fun ty  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let env = FStar_TypeChecker_Env.set_expected_typ goal.context ty in
           let uu____5126 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5126 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let (uvar_env
  :env ->
     FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
       FStar_Syntax_Syntax.term tac)=
  fun env  ->
    fun ty  ->
      let uu____5155 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5161 =
              let uu____5162 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5162 in
            new_uvar env uu____5161 in
      bind uu____5155
        (fun typ  ->
           let uu____5174 = new_uvar env typ in
           bind uu____5174 (fun t  -> ret t))
let (unify
  :FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)=
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5194 =
             FStar_TypeChecker_Rel.teq_nosmt ps.main_context t1 t2 in
           ret uu____5194)
let (goal_of_goal_ty
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       (goal,FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple2)=
  fun env  ->
    fun typ  ->
      let uu____5215 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5215 with
      | (u,uu____5233,g_u) ->
          let g =
            let uu____5248 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____5248 } in
          (g, g_u)
let (proofstate_of_goal_ty
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2)=
  fun env  ->
    fun typ  ->
      let uu____5265 = goal_of_goal_ty env typ in
      match uu____5265 with
      | (g,g_u) ->
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, (g.witness))