open Prims
type debug_level_t =
  | Low
  | Medium
  | High
  | Extreme
  | Other of Prims.string
let uu___is_Low: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | Low  -> true | uu____9 -> false
let uu___is_Medium: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____14 -> false
let uu___is_High: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | High  -> true | uu____19 -> false
let uu___is_Extreme: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____24 -> false
let uu___is_Other: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____30 -> false
let __proj__Other__item___0: debug_level_t -> Prims.string =
  fun projectee  -> match projectee with | Other _0 -> _0
type option_val =
  | Bool of Prims.bool
  | String of Prims.string
  | Path of Prims.string
  | Int of Prims.int
  | List of option_val Prims.list
  | Unset
let uu___is_Bool: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____66 -> false
let __proj__Bool__item___0: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_String: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____80 -> false
let __proj__String__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0
let uu___is_Path: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____94 -> false
let __proj__Path__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0
let uu___is_Int: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____108 -> false
let __proj__Int__item___0: option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0
let uu___is_List: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____124 -> false
let __proj__List__item___0: option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0
let uu___is_Unset: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____143 -> false
let mk_bool: Prims.bool -> option_val = fun _0_28  -> Bool _0_28
let mk_string: Prims.string -> option_val = fun _0_29  -> String _0_29
let mk_path: Prims.string -> option_val = fun _0_30  -> Path _0_30
let mk_int: Prims.int -> option_val = fun _0_31  -> Int _0_31
let mk_list: option_val Prims.list -> option_val = fun _0_32  -> List _0_32
type options =
  | Set
  | Reset
  | Restore
let uu___is_Set: options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____165 -> false
let uu___is_Reset: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____170 -> false
let uu___is_Restore: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____175 -> false
let __unit_tests__: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let __unit_tests: Prims.unit -> Prims.bool =
  fun uu____188  -> FStar_ST.op_Bang __unit_tests__
let __set_unit_tests: Prims.unit -> Prims.unit =
  fun uu____202  -> FStar_ST.op_Colon_Equals __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____216  -> FStar_ST.op_Colon_Equals __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___48_230  ->
    match uu___48_230 with
    | Bool b -> b
    | uu____232 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___49_236  ->
    match uu___49_236 with
    | Int b -> b
    | uu____238 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___50_242  ->
    match uu___50_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___51_251  ->
    match uu___51_251 with
    | List ts -> ts
    | uu____257 -> failwith "Impos: expected List"
let as_list:
  'Auu____266 .
    (option_val -> 'Auu____266) -> option_val -> 'Auu____266 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____282 = as_list' x in
      FStar_All.pipe_right uu____282 (FStar_List.map as_t)
let as_option:
  'Auu____295 .
    (option_val -> 'Auu____295) ->
      option_val -> 'Auu____295 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___52_308  ->
      match uu___52_308 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____312 = as_t v1 in FStar_Pervasives_Native.Some uu____312
type optionstate = option_val FStar_Util.smap
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____331  ->
    let uu____332 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____332
let pop: Prims.unit -> Prims.unit =
  fun uu____356  ->
    let uu____357 = FStar_ST.op_Bang fstar_options in
    match uu____357 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____378::[] -> failwith "TOO MANY POPS!"
    | uu____379::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____404  ->
    let uu____405 =
      let uu____408 =
        let uu____411 = peek () in FStar_Util.smap_copy uu____411 in
      let uu____414 = FStar_ST.op_Bang fstar_options in uu____408 ::
        uu____414 in
    FStar_ST.op_Colon_Equals fstar_options uu____405
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____461 = FStar_ST.op_Bang fstar_options in
    match uu____461 with
    | [] -> failwith "set on empty option stack"
    | uu____482::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____512 = peek () in FStar_Util.smap_add uu____512 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____522  -> match uu____522 with | (k,v1) -> set_option k v1
let with_saved_options: 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____563 =
      let uu____566 = FStar_ST.op_Bang light_off_files in filename ::
        uu____566 in
    FStar_ST.op_Colon_Equals light_off_files uu____563
let defaults:
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("doc", (Bool false));
  ("dump_module", (List []));
  ("eager_inference", (Bool false));
  ("explicit_deps", (Bool false));
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("fstar_home", Unset);
  ("full_context_dependency", (Bool true));
  ("hide_genident_nums", (Bool false));
  ("hide_uvar_nums", (Bool false));
  ("hint_info", (Bool false));
  ("hint_file", Unset);
  ("in", (Bool false));
  ("ide", (Bool false));
  ("include", (List []));
  ("indent", (Bool false));
  ("initial_fuel", (Int (Prims.parse_int "2")));
  ("initial_ifuel", (Int (Prims.parse_int "1")));
  ("lax", (Bool false));
  ("load", (List []));
  ("log_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.parse_int "8")));
  ("max_ifuel", (Int (Prims.parse_int "2")));
  ("min_fuel", (Int (Prims.parse_int "1")));
  ("MLish", (Bool false));
  ("n_cores", (Int (Prims.parse_int "1")));
  ("no_default_includes", (Bool false));
  ("no_extract", (List []));
  ("no_location_info", (Bool false));
  ("odir", Unset);
  ("prims", Unset);
  ("pretype", (Bool true));
  ("prims_ref", Unset);
  ("print_bound_var_types", (Bool false));
  ("print_effect_args", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("query_stats", (Bool false));
  ("record_hints", (Bool false));
  ("reuse_hint_for", Unset);
  ("show_signatures", (List []));
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("split_cases", (Int (Prims.parse_int "0")));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("no_tactics", (Bool false));
  ("using_facts_from", Unset);
  ("verify", (Bool true));
  ("verify_all", (Bool false));
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false))]
let init: Prims.unit -> Prims.unit =
  fun uu____958  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____974  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1024 =
      let uu____1027 = peek () in FStar_Util.smap_try_find uu____1027 s in
    match uu____1024 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1037 . Prims.string -> (option_val -> 'Auu____1037) -> 'Auu____1037
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1054  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1060  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1066  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1072  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1080  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1088  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1096  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1104  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1110  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1114  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1118  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1124  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1130  -> lookup_opt "eager_inference" as_bool
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____1134  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____1138  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1144  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1152  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1158  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1164  -> lookup_opt "fstar_home" (as_option as_string)
let get_hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____1170  -> lookup_opt "hide_genident_nums" as_bool
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1174  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1178  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1184  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1190  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1194  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1200  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1206  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1210  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1214  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1218  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1224  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1230  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1234  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1238  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1242  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1246  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1250  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1254  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1258  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1264  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1270  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1276  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1282  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1288  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1294  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1298  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1302  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1306  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1310  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1314  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1318  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1322  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1326  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1332  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_show_signatures: Prims.unit -> Prims.string Prims.list =
  fun uu____1340  -> lookup_opt "show_signatures" (as_list as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1346  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1352  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1358  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1362  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1366  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1370  -> lookup_opt "split_cases" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1374  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1378  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1382  -> lookup_opt "unthrottle_inductives" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1386  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1390  -> lookup_opt "use_hints" as_bool
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1394  ->
    let uu____1395 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1395
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1403  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____1413  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1419  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1427  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1433  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1437  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1443  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1449  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1453  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1457  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1461  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1465  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1469  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___53_1473  ->
    match uu___53_1473 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1483 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1488 = get_debug_level () in
    FStar_All.pipe_right uu____1488
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1580  ->
    let uu____1581 =
      let uu____1582 = FStar_ST.op_Bang _version in
      let uu____1593 = FStar_ST.op_Bang _platform in
      let uu____1604 = FStar_ST.op_Bang _compiler in
      let uu____1615 = FStar_ST.op_Bang _date in
      let uu____1626 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1582
        uu____1593 uu____1604 uu____1615 uu____1626 in
    FStar_Util.print_string uu____1581
let display_usage_aux:
  'Auu____1643 'Auu____1644 .
    ('Auu____1644,Prims.string,'Auu____1643 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1691  ->
         match uu____1691 with
         | (uu____1702,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1713 =
                      let uu____1714 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____1714 in
                    FStar_Util.print_string uu____1713
                  else
                    (let uu____1716 =
                       let uu____1717 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____1717 doc in
                     FStar_Util.print_string uu____1716)
              | FStar_Getopt.OneArg (uu____1718,argname) ->
                  if doc = ""
                  then
                    let uu____1724 =
                      let uu____1725 = FStar_Util.colorize_bold flag in
                      let uu____1726 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____1725 uu____1726 in
                    FStar_Util.print_string uu____1724
                  else
                    (let uu____1728 =
                       let uu____1729 = FStar_Util.colorize_bold flag in
                       let uu____1730 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1729
                         uu____1730 doc in
                     FStar_Util.print_string uu____1728))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1755 = o in
    match uu____1755 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1785 =
                let uu____1786 = f () in set_option name uu____1786 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1797 = f x in set_option name uu____1797 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____1810 =
        let uu____1813 = lookup_opt name as_list' in value :: uu____1813 in
      mk_list uu____1810
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____1826 =
        let uu____1829 = lookup_opt name as_list' in
        FStar_List.append uu____1829 [value] in
      mk_list uu____1826
let accumulate_string:
  'Auu____1842 .
    Prims.string ->
      ('Auu____1842 -> Prims.string) -> 'Auu____1842 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1860 =
          let uu____1861 =
            let uu____1862 = post_processor value in mk_string uu____1862 in
          accumulated_option name uu____1861 in
        set_option name uu____1860
let add_extract_module: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s
let add_extract_namespace: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s
let add_verify_module: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "verify_module" FStar_String.lowercase s
type opt_type =
  | Const of option_val
  | IntStr of Prims.string
  | BoolStr
  | PathStr of Prims.string
  | SimpleStr of Prims.string
  | EnumStr of Prims.string Prims.list
  | OpenEnumStr of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2
  | PostProcessed of (option_val -> option_val,opt_type)
  FStar_Pervasives_Native.tuple2
  | Accumulated of opt_type
  | ReverseAccumulated of opt_type
  | WithSideEffect of (Prims.unit -> Prims.unit,opt_type)
  FStar_Pervasives_Native.tuple2
let uu___is_Const: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1944 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____1958 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____1971 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____1977 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____1991 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2007 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2033 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2071 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2103 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2117 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2137 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2171 -> true
    | uu____2172 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2180 -> uu____2180
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2197 ->
              let uu____2198 = FStar_Util.int_of_string str_val in
              mk_int uu____2198
          | BoolStr  ->
              let uu____2199 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2199
          | PathStr uu____2202 -> mk_path str_val
          | SimpleStr uu____2203 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2208 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2221 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2221
          | Accumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              accumulated_option opt_name v1
          | ReverseAccumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              reverse_accumulated_option opt_name v1
          | WithSideEffect (side_effect,elem_spec) ->
              (side_effect (); parse_opt_val opt_name elem_spec str_val)
        with
        | InvalidArgument opt_name1 ->
            let uu____2238 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2238
let rec desc_of_opt_type: opt_type -> Prims.string =
  fun typ  ->
    match typ with
    | Const c -> ""
    | IntStr desc -> desc
    | BoolStr  -> FStar_String.concat "|" ["true"; "false"]
    | PathStr desc -> desc
    | SimpleStr desc -> desc
    | EnumStr strs -> FStar_String.concat "|" strs
    | OpenEnumStr (strs,desc) ->
        Prims.strcat (FStar_String.concat "|" strs) (Prims.strcat "|" desc)
    | PostProcessed (uu____2256,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2264,elem_spec) -> desc_of_opt_type elem_spec
let rec nargs_of_opt_type: opt_type -> Prims.int =
  fun typ  ->
    match typ with
    | Const uu____2274 -> Prims.parse_int "0"
    | IntStr uu____2275 -> Prims.parse_int "1"
    | BoolStr  -> Prims.parse_int "1"
    | PathStr uu____2276 -> Prims.parse_int "1"
    | SimpleStr uu____2277 -> Prims.parse_int "1"
    | EnumStr uu____2278 -> Prims.parse_int "1"
    | OpenEnumStr uu____2281 -> Prims.parse_int "1"
    | PostProcessed (uu____2288,elem_spec) -> nargs_of_opt_type elem_spec
    | Accumulated elem_spec -> nargs_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> nargs_of_opt_type elem_spec
    | WithSideEffect (uu____2296,elem_spec) -> nargs_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let nargs = nargs_of_opt_type typ in
      let parser = parse_opt_val opt_name typ in
      match nargs with
      | _0_33 when _0_33 = (Prims.parse_int "0") ->
          FStar_Getopt.ZeroArgs ((fun uu____2321  -> parser ""))
      | uu____2322 ->
          let desc = desc_of_opt_type typ in
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2336 =
      let uu____2337 = as_string s in FStar_String.lowercase uu____2337 in
    mk_string uu____2336
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2354  ->
    let uu____2365 =
      let uu____2376 =
        let uu____2387 =
          let uu____2398 =
            let uu____2409 =
              let uu____2420 =
                let uu____2431 =
                  let uu____2442 =
                    let uu____2453 =
                      let uu____2462 =
                        let uu____2463 = mk_bool true in Const uu____2463 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2462,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2464 =
                      let uu____2475 =
                        let uu____2484 =
                          let uu____2485 = mk_bool true in Const uu____2485 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2484,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____2486 =
                        let uu____2497 =
                          let uu____2506 =
                            let uu____2507 = mk_bool true in Const uu____2507 in
                          (FStar_Getopt.noshort, "doc", uu____2506,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____2508 =
                          let uu____2519 =
                            let uu____2530 =
                              let uu____2539 =
                                let uu____2540 = mk_bool true in
                                Const uu____2540 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____2539,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____2541 =
                              let uu____2552 =
                                let uu____2561 =
                                  let uu____2562 = mk_bool true in
                                  Const uu____2562 in
                                (FStar_Getopt.noshort, "explicit_deps",
                                  uu____2561,
                                  "Do not find dependencies automatically, the user provides them on the command-line") in
                              let uu____2563 =
                                let uu____2574 =
                                  let uu____2583 =
                                    let uu____2584 = mk_bool true in
                                    Const uu____2584 in
                                  (FStar_Getopt.noshort, "extract_all",
                                    uu____2583,
                                    "Discover the complete dependency graph and do not stop at interface boundaries") in
                                let uu____2585 =
                                  let uu____2596 =
                                    let uu____2607 =
                                      let uu____2618 =
                                        let uu____2629 =
                                          let uu____2638 =
                                            let uu____2639 = mk_bool true in
                                            Const uu____2639 in
                                          (FStar_Getopt.noshort,
                                            "hide_genident_nums", uu____2638,
                                            "Don't print generated identifier numbers") in
                                        let uu____2640 =
                                          let uu____2651 =
                                            let uu____2660 =
                                              let uu____2661 = mk_bool true in
                                              Const uu____2661 in
                                            (FStar_Getopt.noshort,
                                              "hide_uvar_nums", uu____2660,
                                              "Don't print unification variable numbers") in
                                          let uu____2662 =
                                            let uu____2673 =
                                              let uu____2684 =
                                                let uu____2693 =
                                                  let uu____2694 =
                                                    mk_bool true in
                                                  Const uu____2694 in
                                                (FStar_Getopt.noshort,
                                                  "hint_info", uu____2693,
                                                  "Print information regarding hints (deprecated; use --query_stats instead)") in
                                              let uu____2695 =
                                                let uu____2706 =
                                                  let uu____2715 =
                                                    let uu____2716 =
                                                      mk_bool true in
                                                    Const uu____2716 in
                                                  (FStar_Getopt.noshort,
                                                    "in", uu____2715,
                                                    "Legacy interactive mode; reads input from stdin") in
                                                let uu____2717 =
                                                  let uu____2728 =
                                                    let uu____2737 =
                                                      let uu____2738 =
                                                        mk_bool true in
                                                      Const uu____2738 in
                                                    (FStar_Getopt.noshort,
                                                      "ide", uu____2737,
                                                      "JSON-based interactive mode for IDEs") in
                                                  let uu____2739 =
                                                    let uu____2750 =
                                                      let uu____2761 =
                                                        let uu____2770 =
                                                          let uu____2771 =
                                                            mk_bool true in
                                                          Const uu____2771 in
                                                        (FStar_Getopt.noshort,
                                                          "indent",
                                                          uu____2770,
                                                          "Parses and outputs the files on the command line") in
                                                      let uu____2772 =
                                                        let uu____2783 =
                                                          let uu____2794 =
                                                            let uu____2805 =
                                                              let uu____2814
                                                                =
                                                                let uu____2815
                                                                  =
                                                                  mk_bool
                                                                    true in
                                                                Const
                                                                  uu____2815 in
                                                              (FStar_Getopt.noshort,
                                                                "lax",
                                                                uu____2814,
                                                                "Run the lax-type checker only (admit all verification conditions)") in
                                                            let uu____2816 =
                                                              let uu____2827
                                                                =
                                                                let uu____2838
                                                                  =
                                                                  let uu____2847
                                                                    =
                                                                    let uu____2848
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2848 in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2847,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                let uu____2849
                                                                  =
                                                                  let uu____2860
                                                                    =
                                                                    let uu____2869
                                                                    =
                                                                    let uu____2870
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2870 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2869,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                  let uu____2871
                                                                    =
                                                                    let uu____2882
                                                                    =
                                                                    let uu____2893
                                                                    =
                                                                    let uu____2904
                                                                    =
                                                                    let uu____2915
                                                                    =
                                                                    let uu____2924
                                                                    =
                                                                    let uu____2925
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2925 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2924,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____2926
                                                                    =
                                                                    let uu____2937
                                                                    =
                                                                    let uu____2948
                                                                    =
                                                                    let uu____2957
                                                                    =
                                                                    let uu____2958
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2958 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____2957,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____2959
                                                                    =
                                                                    let uu____2970
                                                                    =
                                                                    let uu____2981
                                                                    =
                                                                    let uu____2990
                                                                    =
                                                                    let uu____2991
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2991 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____2990,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____2992
                                                                    =
                                                                    let uu____3003
                                                                    =
                                                                    let uu____3014
                                                                    =
                                                                    let uu____3025
                                                                    =
                                                                    let uu____3034
                                                                    =
                                                                    let uu____3035
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3035 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3034,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3036
                                                                    =
                                                                    let uu____3047
                                                                    =
                                                                    let uu____3056
                                                                    =
                                                                    let uu____3057
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3057 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3056,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3058
                                                                    =
                                                                    let uu____3069
                                                                    =
                                                                    let uu____3078
                                                                    =
                                                                    let uu____3079
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3079 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3078,
                                                                    "Print full names of variables") in
                                                                    let uu____3080
                                                                    =
                                                                    let uu____3091
                                                                    =
                                                                    let uu____3100
                                                                    =
                                                                    let uu____3101
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3101 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3100,
                                                                    "Print implicit arguments") in
                                                                    let uu____3102
                                                                    =
                                                                    let uu____3113
                                                                    =
                                                                    let uu____3122
                                                                    =
                                                                    let uu____3123
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3123 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3122,
                                                                    "Print universes") in
                                                                    let uu____3124
                                                                    =
                                                                    let uu____3135
                                                                    =
                                                                    let uu____3144
                                                                    =
                                                                    let uu____3145
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3145 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3144,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3146
                                                                    =
                                                                    let uu____3157
                                                                    =
                                                                    let uu____3166
                                                                    =
                                                                    let uu____3167
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3167 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3166,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3168
                                                                    =
                                                                    let uu____3179
                                                                    =
                                                                    let uu____3188
                                                                    =
                                                                    let uu____3189
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3189 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3188,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3190
                                                                    =
                                                                    let uu____3201
                                                                    =
                                                                    let uu____3210
                                                                    =
                                                                    let uu____3211
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3211 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3210,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3212
                                                                    =
                                                                    let uu____3223
                                                                    =
                                                                    let uu____3234
                                                                    =
                                                                    let uu____3245
                                                                    =
                                                                    let uu____3254
                                                                    =
                                                                    let uu____3255
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3255 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3254,
                                                                    " ") in
                                                                    let uu____3256
                                                                    =
                                                                    let uu____3267
                                                                    =
                                                                    let uu____3278
                                                                    =
                                                                    let uu____3289
                                                                    =
                                                                    let uu____3300
                                                                    =
                                                                    let uu____3311
                                                                    =
                                                                    let uu____3322
                                                                    =
                                                                    let uu____3331
                                                                    =
                                                                    let uu____3332
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3332 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3331,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3333
                                                                    =
                                                                    let uu____3344
                                                                    =
                                                                    let uu____3353
                                                                    =
                                                                    let uu____3354
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3354 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3353,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3355
                                                                    =
                                                                    let uu____3366
                                                                    =
                                                                    let uu____3375
                                                                    =
                                                                    let uu____3376
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3376 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3375,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3377
                                                                    =
                                                                    let uu____3388
                                                                    =
                                                                    let uu____3397
                                                                    =
                                                                    let uu____3398
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3398 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3397,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3399
                                                                    =
                                                                    let uu____3410
                                                                    =
                                                                    let uu____3419
                                                                    =
                                                                    let uu____3420
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3420 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3419,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3421
                                                                    =
                                                                    let uu____3432
                                                                    =
                                                                    let uu____3441
                                                                    =
                                                                    let uu____3442
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3442 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3441,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3443
                                                                    =
                                                                    let uu____3454
                                                                    =
                                                                    let uu____3463
                                                                    =
                                                                    let uu____3464
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3464 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3463,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3465
                                                                    =
                                                                    let uu____3476
                                                                    =
                                                                    let uu____3487
                                                                    =
                                                                    let uu____3496
                                                                    =
                                                                    let uu____3497
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3497 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_all",
                                                                    uu____3496,
                                                                    "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.") in
                                                                    let uu____3498
                                                                    =
                                                                    let uu____3509
                                                                    =
                                                                    let uu____3520
                                                                    =
                                                                    let uu____3531
                                                                    =
                                                                    let uu____3540
                                                                    =
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3548
                                                                    =
                                                                    let uu____3549
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3549 in
                                                                    ((fun
                                                                    uu____3554
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3548) in
                                                                    WithSideEffect
                                                                    uu____3541 in
                                                                    ('v',
                                                                    "version",
                                                                    uu____3540,
                                                                    "Display version number") in
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3567
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3577 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3576,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    let uu____3609
                                                                    =
                                                                    let uu____3610
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3610 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3609,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3622
                                                                    =
                                                                    let uu____3633
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3655
                                                                    =
                                                                    let uu____3664
                                                                    =
                                                                    let uu____3665
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3665 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3664,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____3666
                                                                    =
                                                                    let uu____3677
                                                                    =
                                                                    let uu____3686
                                                                    =
                                                                    let uu____3687
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3687 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3686,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____3688
                                                                    =
                                                                    let uu____3699
                                                                    =
                                                                    let uu____3708
                                                                    =
                                                                    let uu____3709
                                                                    =
                                                                    let uu____3716
                                                                    =
                                                                    let uu____3717
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3717 in
                                                                    ((fun
                                                                    uu____3722
                                                                     ->
                                                                    (
                                                                    let uu____3724
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____3724);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3716) in
                                                                    WithSideEffect
                                                                    uu____3709 in
                                                                    ('h',
                                                                    "help",
                                                                    uu____3708,
                                                                    "Display this information") in
                                                                    [uu____3699] in
                                                                    uu____3677
                                                                    ::
                                                                    uu____3688 in
                                                                    uu____3655
                                                                    ::
                                                                    uu____3666 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3644 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3633 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3622 in
                                                                    uu____3600
                                                                    ::
                                                                    uu____3611 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3589 in
                                                                    uu____3567
                                                                    ::
                                                                    uu____3578 in
                                                                    uu____3531
                                                                    ::
                                                                    uu____3556 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3520 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_module",
                                                                    (Accumulated
                                                                    (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "module name")))),
                                                                    "Name of the module to verify")
                                                                    ::
                                                                    uu____3509 in
                                                                    uu____3487
                                                                    ::
                                                                    uu____3498 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu____3862
                                                                     ->
                                                                    set_option
                                                                    "z3refresh"
                                                                    (Bool
                                                                    true)),
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "namespace | fact id")))),
                                                                    "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids")
                                                                    ::
                                                                    uu____3476 in
                                                                    uu____3454
                                                                    ::
                                                                    uu____3465 in
                                                                    uu____3432
                                                                    ::
                                                                    uu____3443 in
                                                                    uu____3410
                                                                    ::
                                                                    uu____3421 in
                                                                    uu____3388
                                                                    ::
                                                                    uu____3399 in
                                                                    uu____3366
                                                                    ::
                                                                    uu____3377 in
                                                                    uu____3344
                                                                    ::
                                                                    uu____3355 in
                                                                    uu____3322
                                                                    ::
                                                                    uu____3333 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive integer"),
                                                                    "Partition VC of a match into groups of [n] cases")
                                                                    ::
                                                                    uu____3311 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3300 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3289 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3278 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3267 in
                                                                    uu____3245
                                                                    ::
                                                                    uu____3256 in
                                                                    (FStar_Getopt.noshort,
                                                                    "show_signatures",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module name")),
                                                                    "Show the checked signatures for all top-level symbols in the module")
                                                                    ::
                                                                    uu____3234 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "top-level name in the current module"),
                                                                    "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3223 in
                                                                    uu____3201
                                                                    ::
                                                                    uu____3212 in
                                                                    uu____3179
                                                                    ::
                                                                    uu____3190 in
                                                                    uu____3157
                                                                    ::
                                                                    uu____3168 in
                                                                    uu____3135
                                                                    ::
                                                                    uu____3146 in
                                                                    uu____3113
                                                                    ::
                                                                    uu____3124 in
                                                                    uu____3091
                                                                    ::
                                                                    uu____3102 in
                                                                    uu____3069
                                                                    ::
                                                                    uu____3080 in
                                                                    uu____3047
                                                                    ::
                                                                    uu____3058 in
                                                                    uu____3025
                                                                    ::
                                                                    uu____3036 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3014 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3003 in
                                                                    uu____2981
                                                                    ::
                                                                    uu____2992 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____2970 in
                                                                    uu____2948
                                                                    ::
                                                                    uu____2959 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "[positive integer]"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____2937 in
                                                                    uu____2915
                                                                    ::
                                                                    uu____2926 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2904 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2893 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2882 in
                                                                  uu____2860
                                                                    ::
                                                                    uu____2871 in
                                                                uu____2838 ::
                                                                  uu____2849 in
                                                              (FStar_Getopt.noshort,
                                                                "load",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "module")),
                                                                "Load compiled module")
                                                                :: uu____2827 in
                                                            uu____2805 ::
                                                              uu____2816 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_ifuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                            :: uu____2794 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_fuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of recursive functions to try initially (default 2)")
                                                          :: uu____2783 in
                                                      uu____2761 ::
                                                        uu____2772 in
                                                    (FStar_Getopt.noshort,
                                                      "include",
                                                      (ReverseAccumulated
                                                         (PathStr "path")),
                                                      "A directory in which to search for files included on the command line")
                                                      :: uu____2750 in
                                                  uu____2728 :: uu____2739 in
                                                uu____2706 :: uu____2717 in
                                              uu____2684 :: uu____2695 in
                                            (FStar_Getopt.noshort,
                                              "hint_file", (PathStr "path"),
                                              "Read/write hints to <path> (instead of module-specific hints files)")
                                              :: uu____2673 in
                                          uu____2651 :: uu____2662 in
                                        uu____2629 :: uu____2640 in
                                      (FStar_Getopt.noshort, "fstar_home",
                                        (PathStr "dir"),
                                        "Set the FSTAR_HOME variable to <dir>")
                                        :: uu____2618 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Only extract modules in the specified namespace")
                                      :: uu____2607 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module name")))),
                                    "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____2596 in
                                uu____2574 :: uu____2585 in
                              uu____2552 :: uu____2563 in
                            uu____2530 :: uu____2541 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module name")), "") ::
                            uu____2519 in
                        uu____2497 :: uu____2508 in
                      uu____2475 :: uu____2486 in
                    uu____2453 :: uu____2464 in
                  (FStar_Getopt.noshort, "dep", (EnumStr ["make"; "graph"]),
                    "Output the transitive closure of the dependency graph in a format suitable for the given tool")
                    :: uu____2442 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2431 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module name")),
                "Print lots of debugging information while checking module")
                :: uu____2420 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2409 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"]),
            "Generate code for execution") :: uu____2398 in
        (FStar_Getopt.noshort, "cache_checked_modules", (Const (Bool true)),
          "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
          :: uu____2387 in
      (FStar_Getopt.noshort, "admit_except", (SimpleStr "[id]"),
        "Admit all verification conditions, except those with query label <id> (eg, --admit_except '(FStar.Fin.pigeonhole, 1)'")
        :: uu____2376 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2365
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4399  ->
    let uu____4402 = specs_with_types () in
    FStar_List.map
      (fun uu____4427  ->
         match uu____4427 with
         | (short,long,typ,doc) ->
             let uu____4440 =
               let uu____4451 = arg_spec_of_opt_type long typ in
               (short, long, uu____4451, doc) in
             mk_spec uu____4440) uu____4402
let settable: Prims.string -> Prims.bool =
  fun uu___54_4459  ->
    match uu___54_4459 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "hide_genident_nums" -> true
    | "hide_uvar_nums" -> true
    | "hint_info" -> true
    | "hint_file" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "lax" -> true
    | "log_types" -> true
    | "log_queries" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "min_fuel" -> true
    | "ugly" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
    | "query_stats" -> true
    | "show_signatures" -> true
    | "silent" -> true
    | "smtencoding.elim_box" -> true
    | "smtencoding.nl_arith_repr" -> true
    | "smtencoding.l_arith_repr" -> true
    | "split_cases" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "no_tactics" -> true
    | "using_facts_from" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | uu____4460 -> false
let resettable: Prims.string -> Prims.bool =
  fun s  -> ((settable s) || (s = "z3seed")) || (s = "z3cliopt")
let all_specs: FStar_Getopt.opt Prims.list = specs ()
let all_specs_with_types:
  (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list
  = specs_with_types ()
let settable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4518  ->
          match uu____4518 with
          | (uu____4529,x,uu____4531,uu____4532) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4578  ->
          match uu____4578 with
          | (uu____4589,x,uu____4591,uu____4592) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____4600  ->
    let uu____4601 = specs () in display_usage_aux uu____4601
let fstar_home: Prims.unit -> Prims.string =
  fun uu____4617  ->
    let uu____4618 = get_fstar_home () in
    match uu____4618 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____4624 =
            let uu____4629 = mk_string x1 in ("fstar_home", uu____4629) in
          set_option' uu____4624);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____4638 -> true
    | uu____4639 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____4647 -> uu____4647
let set_options: options -> Prims.string -> FStar_Getopt.parse_cmdline_res =
  fun o  ->
    fun s  ->
      let specs1 =
        match o with
        | Set  -> settable_specs
        | Reset  -> resettable_specs
        | Restore  -> all_specs in
      try
        if s = ""
        then FStar_Getopt.Success
        else
          FStar_Getopt.parse_string specs1
            (fun s1  -> FStar_Exn.raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____4693 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____4693
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4716  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____4721 =
             let uu____4724 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____4724 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____4721) in
    let uu____4763 =
      let uu____4766 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____4766 in
    (res, uu____4763)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____4794  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____4823 = specs () in
       FStar_Getopt.parse_cmdline uu____4823 (fun x  -> ()) in
     (let uu____4829 =
        let uu____4834 =
          let uu____4835 = FStar_List.map mk_string old_verify_module in
          List uu____4835 in
        ("verify_module", uu____4834) in
      set_option' uu____4829);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____4844 =
        let uu____4845 =
          let uu____4846 =
            let uu____4847 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____4847 in
          (FStar_String.length f1) - uu____4846 in
        uu____4845 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____4844 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____4852 = get_lax () in
    if uu____4852
    then false
    else
      (let uu____4854 = get_verify_all () in
       if uu____4854
       then true
       else
         (let uu____4856 = get_verify_module () in
          match uu____4856 with
          | [] ->
              let uu____4859 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let uu____4865 = module_name_of_file_name f in
                   uu____4865 = m) uu____4859
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____4873 = module_name_of_file_name fn in should_verify uu____4873
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____4878 = get___temp_no_proj () in
    FStar_List.contains m uu____4878
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____4885 = should_verify m in
    if uu____4885 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____4892  ->
    let uu____4893 = get_no_default_includes () in
    if uu____4893
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____4901 =
         let uu____4904 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____4904
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____4917 =
         let uu____4920 = get_include () in
         FStar_List.append uu____4920 ["."] in
       FStar_List.append uu____4901 uu____4917)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____4929 = FStar_Util.is_path_absolute filename in
    if uu____4929
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____4936 =
         let uu____4939 = include_path () in FStar_List.rev uu____4939 in
       FStar_Util.find_map uu____4936
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____4952  ->
    let uu____4953 = get_prims () in
    match uu____4953 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____4957 = find_file filename in
        (match uu____4957 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____4961 =
               let uu____4962 =
                 FStar_Util.format1
                   "unable to find required file \"%s\" in the module search path.\n"
                   filename in
               FStar_Util.Failure uu____4962 in
             FStar_Exn.raise uu____4961)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____4967  ->
    let uu____4968 = prims () in FStar_Util.basename uu____4968
let pervasives: Prims.unit -> Prims.string =
  fun uu____4972  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____4974 = find_file filename in
    match uu____4974 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____4978 =
          let uu____4979 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename in
          FStar_Util.Failure uu____4979 in
        FStar_Exn.raise uu____4978
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____4983  ->
    let uu____4984 = pervasives () in FStar_Util.basename uu____4984
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____4988  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____4990 = find_file filename in
    match uu____4990 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____4994 =
          let uu____4995 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename in
          FStar_Util.Failure uu____4995 in
        FStar_Exn.raise uu____4994
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5000 = get_odir () in
    match uu____5000 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5008 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5008 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5016  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5022  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5026  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5032  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5040  ->
    let uu____5041 = get_codegen_lib () in
    FStar_All.pipe_right uu____5041
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5057  -> let uu____5058 = get_debug () in uu____5058 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5073 = get_debug () in
       FStar_All.pipe_right uu____5073 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5083  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5087  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5091  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5095  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5100 = get_dump_module () in
    FStar_All.pipe_right uu____5100 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5108  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____5112  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____5116  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5121 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5121
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5145  -> true
let hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____5149  -> get_hide_genident_nums ()
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5153  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5157  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5163  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5167  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5171  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5175  ->
    let uu____5176 = get_initial_fuel () in
    let uu____5177 = get_max_fuel () in Prims.min uu____5176 uu____5177
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5181  ->
    let uu____5182 = get_initial_ifuel () in
    let uu____5183 = get_max_ifuel () in Prims.min uu____5182 uu____5183
let interactive: Prims.unit -> Prims.bool =
  fun uu____5187  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5191  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5197  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5201  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5205  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5209  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5213  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5217  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5221  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5225  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5229  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5233  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5237  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5242 = get_no_extract () in
    FStar_All.pipe_right uu____5242 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5250  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5256  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5260  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5264  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5268  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5272  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5276  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5280  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5284  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5288  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5292  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5298  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5302  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5306  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5310  ->
    let uu____5311 = get_smtencoding_nl_arith_repr () in
    uu____5311 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5315  ->
    let uu____5316 = get_smtencoding_nl_arith_repr () in
    uu____5316 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5320  ->
    let uu____5321 = get_smtencoding_nl_arith_repr () in
    uu____5321 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5325  ->
    let uu____5326 = get_smtencoding_l_arith_repr () in uu____5326 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5330  ->
    let uu____5331 = get_smtencoding_l_arith_repr () in
    uu____5331 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____5335  -> get_split_cases ()
let timing: Prims.unit -> Prims.bool = fun uu____5339  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5343  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5347  -> get_unthrottle_inductives ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5351  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____5355  -> get_use_hints ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____5359  -> get_use_tactics ()
let using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____5367  -> get_using_facts_from ()
let verify_all: Prims.unit -> Prims.bool =
  fun uu____5371  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____5377  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____5381  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____5385  ->
    let uu____5386 = get_smt () in
    match uu____5386 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____5395  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____5399  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____5403  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____5407  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____5411  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____5415  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____5419  -> get_ml_no_eta_expand_coertions ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____5426 = no_extract m in Prims.op_Negation uu____5426) &&
      ((extract_all ()) ||
         (let uu____5429 = get_extract_module () in
          match uu____5429 with
          | [] ->
              let uu____5432 = get_extract_namespace () in
              (match uu____5432 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))