
open Prims

type file =
(Prims.string * FStar_Extraction_JavaScript_Ast.t)


type env =
{names : name Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; module_name = module_name})


let mk_op_bin : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_bin Prims.option = (fun _82_1 -> (match (_82_1) with
| "op_Addition" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Plus)
end
| "op_Subtraction" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Minus)
end
| "op_Multiply" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Mult)
end
| "op_Division" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Div)
end
| "op_Equality" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Equal)
end
| "op_disEquality" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_NotEqual)
end
| "op_LessThanOrEqual" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_LessThanEqual)
end
| "op_GreaterThanOrEqual" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_GreaterThanEqual)
end
| "op_LessThan" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_LessThan)
end
| "op_GreaterThan" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_GreaterThan)
end
| "op_Modulus" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Mod)
end
| _82_25 -> begin
None
end))


let is_op_bin : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bin op) <> None))


let mk_op_un : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_un Prims.option = (fun _82_2 -> (match (_82_2) with
| "op_Negation" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Not)
end
| "op_Minus" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Minus)
end
| "op_Bang" -> begin
(FStar_All.failwith "todo: translation [!]")
end
| _82_32 -> begin
None
end))


let is_op_un : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_un op) <> None))


let mk_op_bool : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_log Prims.option = (fun _82_3 -> (match (_82_3) with
| "op_AmpAmp" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_And)
end
| "op_BarBar" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_Or)
end
| _82_38 -> begin
None
end))


let is_op_bool : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bool op) <> None))


let mk_standart_type : Prims.string  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option = (fun _82_4 -> (match (_82_4) with
| "unit" -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_Null)
end
| "bool" -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_Boolean)
end
| ("int") | ("nat") -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_Number)
end
| "string" -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_String)
end
| _82_47 -> begin
None
end))


let is_standart_type : Prims.string  ->  Prims.bool = (fun t -> ((mk_standart_type t) <> None))


let is_prim_constructors : Prims.string  ->  Prims.bool = (fun s -> (FStar_List.existsb (fun x -> (x = s)) (("Cons")::("Nil")::("Some")::("None")::[])))


let float_of_int : Prims.int  ->  FStar_BaseTypes.float = (fun i -> (FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)))


let export_modules : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let current_module_name : Prims.string FStar_ST.ref = (FStar_ST.alloc "")


let getName = (fun _82_54 -> (match (_82_54) with
| (path, n) -> begin
(

let path = (FStar_String.concat "_" path)
in if ((path = (FStar_ST.read current_module_name)) || (path = "")) then begin
((n), (None))
end else begin
(

let _82_57 = if (not ((let _179_40 = (FStar_ST.read export_modules)
in (FStar_List.existsb (fun x -> (x = path)) _179_40)))) then begin
(let _179_42 = (let _179_41 = (FStar_ST.read export_modules)
in (FStar_List.append ((path)::[]) _179_41))
in (FStar_ST.op_Colon_Equals export_modules _179_42))
end else begin
()
end
in (((Prims.strcat path (Prims.strcat "." n))), (None)))
end)
end))


let rec is_pure_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, _82_71) -> begin
(is_pure_expr expr)
end
| FStar_Extraction_ML_Syntax.MLE_CTor (p, le) -> begin
(not ((let _179_45 = (FStar_List.map is_pure_expr le)
in (FStar_List.contains false _179_45))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (le) -> begin
(not ((let _179_46 = (FStar_List.map is_pure_expr le)
in (FStar_List.contains false _179_46))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_81, lne) -> begin
(not ((let _179_48 = (FStar_List.map (fun _82_87 -> (match (_82_87) with
| (n, e) -> begin
(is_pure_expr e)
end)) lne)
in (FStar_List.contains false _179_48))))
end
| FStar_Extraction_ML_Syntax.MLE_App (_82_89, args) -> begin
(not ((let _179_49 = (FStar_List.map is_pure_expr args)
in (FStar_List.contains false _179_49))))
end
| _82_94 -> begin
false
end))


let rec get_Generic : FStar_Extraction_JavaScript_Ast.typ  ->  Prims.string Prims.list = (fun t -> (match (t) with
| FStar_Extraction_JavaScript_Ast.JST_Generic (g, v) -> begin
(match (v) with
| Some (v1) -> begin
(FStar_List.collect get_Generic v1)
end
| None -> begin
(match (g) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _82_105) -> begin
if ((FStar_String.get id (Prims.parse_int "0")) = '\'') then begin
(id)::[]
end else begin
[]
end
end
| _82_109 -> begin
[]
end)
end)
end
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_111, _82_113, gen_d) -> begin
(match (gen_d) with
| Some (v) -> begin
v
end
| None -> begin
[]
end)
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(FStar_List.collect get_Generic lt)
end
| FStar_Extraction_JavaScript_Ast.JST_Object (l, _82_124, _82_126) -> begin
(FStar_List.collect (fun _82_132 -> (match (_82_132) with
| (_82_130, t) -> begin
(get_Generic t)
end)) l)
end
| _82_134 -> begin
[]
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_136 -> (match (_82_136) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_145 = m
in (match (_82_145) with
| ((prefix, final), _82_142, _82_144) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_155 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (

let _82_157 = (FStar_ST.op_Colon_Equals export_modules [])
in (let _179_80 = (translate_module m)
in Some (_179_80))))
end)
with
| e -> begin
(

let _82_151 = (let _179_82 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_82))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_163 -> (match (_82_163) with
| (module_name, modul, _82_162) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let _82_169 = (FStar_ST.op_Colon_Equals current_module_name (FStar_String.concat "_" module_name))
in (

let res = (FStar_List.filter_map translate_decl decls)
in (

let create_module_exports = (

let require_f = (fun m -> FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("require"), (None)))), ((FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((Prims.strcat "./" m))), (""))))::[]))))
in (let _179_91 = (let _179_89 = (let _179_87 = (FStar_ST.read export_modules)
in (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((m), (None)))), (Some ((require_f m)))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))) _179_87))
in (FStar_All.pipe_right _179_89 (fun _179_88 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_88))))
in (FStar_All.pipe_right _179_91 (fun _179_90 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_90)))))
in (FStar_List.append ((create_module_exports)::[]) res))))
end
| _82_177 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_82_181, c_flag, lfunc) -> begin
(

let for1 = (fun _82_195 -> (match (_82_195) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _82_193); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_96 = (translate_type ty)
in (FStar_All.pipe_right _179_96 (fun _179_95 -> Some (_179_95))))
end
| Some (lp, ty) -> begin
(match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_207, t2) -> begin
(

let lp = (match (lp) with
| [] -> begin
None
end
| _82_213 -> begin
(let _179_99 = (FStar_List.map (fun _82_217 -> (match (_82_217) with
| (id, _82_216) -> begin
id
end)) lp)
in (FStar_All.pipe_right _179_99 (fun _179_98 -> Some (_179_98))))
end)
in if unit_b then begin
None
end else begin
(let _179_106 = (let _179_104 = (let _179_103 = (let _179_101 = (let _179_100 = (translate_type t1)
in (((("_1"), (None))), (_179_100)))
in (_179_101)::[])
in (let _179_102 = (translate_type t2)
in ((_179_103), (_179_102), (lp))))
in FStar_Extraction_JavaScript_Ast.JST_Function (_179_104))
in (FStar_All.pipe_right _179_106 (fun _179_105 -> Some (_179_105))))
end)
end
| _82_220 -> begin
None
end)
end)
end
in (

let is_private = (FStar_List.contains FStar_Extraction_ML_Syntax.Private c_flag)
in (

let expr = if (is_pure_expr expr) then begin
(let _179_112 = (let _179_111 = (let _179_110 = (let _179_109 = (let _179_108 = (let _179_107 = (translate_expr_pure expr)
in Some (_179_107))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_179_108)))
in (_179_109)::[])
in ((_179_110), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_111))
in (_179_112)::[])
end else begin
(let _179_114 = (let _179_113 = (translate_expr expr ((name), (t)) None)
in (_179_113)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::_179_114)
end
in if is_private then begin
expr
end else begin
(let _179_117 = (let _179_116 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Expression (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("exports"), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier (((name), (None)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None))))))) (fun _179_115 -> FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_115)))
in (_179_116)::[])
in (FStar_List.append expr _179_117))
end)))
end))
in (let _179_123 = (let _179_121 = (let _179_119 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _179_119 (fun _179_118 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_118))))
in (FStar_All.pipe_right _179_121 (fun _179_120 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_120))))
in (FStar_All.pipe_right _179_123 (fun _179_122 -> Some (_179_122)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_225) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_228, name, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _82_237 -> begin
(let _179_126 = (FStar_List.map (fun _82_241 -> (match (_82_241) with
| (id, _82_240) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _179_126 (fun _179_125 -> Some (_179_125))))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_130 = (let _179_129 = (translate_type t)
in ((((name), (None))), (tparams), (_179_129)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_130))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_252 -> (match (_82_252) with
| (n, t) -> begin
(let _179_132 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_132)))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _179_143 = (let _179_141 = (let _179_140 = (let _179_139 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_139))
in ((_179_140), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_141))
in (let _179_142 = (translate_type t)
in ((_179_143), (_179_142))))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_264 -> (match (_82_264) with
| (n, l) -> begin
(let _179_149 = (let _179_148 = (let _179_147 = (let _179_146 = (let _179_145 = (fields_t l)
in (FStar_List.append (tag n) _179_145))
in ((_179_146), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_147))
in ((((n), (None))), (tparams), (_179_148)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_149))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _179_152 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _179_152 (fun _179_151 -> Some (_179_151))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _82_273 -> (match (_82_273) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((n), (None)))), (tparams_gen)))
end)) lfields)
in (

let union_t = FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append lfields_t ((union_t)::[])))))))))
end))
in (

let body_t = (match (body) with
| None -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty] with empty body")
end
| Some (v) -> begin
(forbody v)
end)
in (let _179_156 = (FStar_All.pipe_right body_t (fun _179_154 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_154)))
in (FStar_All.pipe_right _179_156 (fun _179_155 -> Some (_179_155)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_281) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_284) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _179_159 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _179_157 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_157)))
in (FStar_All.pipe_right _179_159 (fun _179_158 -> Some (_179_158))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_291) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e) -> begin
(

let c = (let _179_165 = (let _179_164 = (let _179_163 = (translate_expr_pure e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_163)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_164))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_165))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_302, _82_304, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_311); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let c = if (is_pure_expr body) then begin
(let _179_173 = (let _179_170 = (let _179_169 = (let _179_168 = (let _179_167 = (let _179_166 = (translate_expr_pure body)
in Some (_179_166))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_179_167)))
in (_179_168)::[])
in ((_179_169), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_170))
in (let _179_172 = (let _179_171 = (translate_expr continuation var stmt)
in (_179_171)::[])
in (_179_173)::_179_172))
end else begin
(let _179_177 = (let _179_176 = (let _179_175 = (let _179_174 = (translate_expr continuation var stmt)
in Some (_179_174))
in (translate_expr body ((name), (None)) _179_175))
in (_179_176)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_177)
end
in FStar_Extraction_JavaScript_Ast.JSS_Block (c))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_321) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let generic_t = (FStar_ST.alloc [])
in (

let addUnique = (fun lst -> (FStar_List.map (fun el -> if (not ((let _179_182 = (FStar_ST.read generic_t)
in (FStar_List.existsb (fun x -> (x = el)) _179_182)))) then begin
(let _179_184 = (let _179_183 = (FStar_ST.read generic_t)
in (FStar_List.append ((el)::[]) _179_183))
in (FStar_ST.op_Colon_Equals generic_t _179_184))
end else begin
()
end) lst))
in (

let args = (FStar_List.map (fun _82_337 -> (match (_82_337) with
| ((n, _82_334), t) -> begin
(

let t = (translate_type t)
in (

let _82_339 = (let _179_187 = (let _179_186 = (get_Generic t)
in (addUnique _179_186))
in (FStar_All.pipe_right _179_187 Prims.ignore))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (Some (t))))))
end)) args)
in (

let generic_r = (match ((FStar_ST.read generic_t)) with
| [] -> begin
None
end
| _82_344 -> begin
(let _179_188 = (FStar_ST.read generic_t)
in Some (_179_188))
end)
in (

let body_t = if (is_pure_expr body) then begin
(let _179_189 = (translate_expr_pure body)
in FStar_Extraction_JavaScript_Ast.JS_BodyExpression (_179_189))
end else begin
(let _179_192 = (let _179_191 = (let _179_190 = (translate_expr body (("_res"), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))))
in (_179_190)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_191)
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_179_192))
end
in (

let ret_t = (match ((Prims.snd var)) with
| None -> begin
None
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_351, t2, _82_354) -> begin
Some (t2)
end
| _82_358 -> begin
None
end)
end)
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (((None), (args), (body_t), (ret_t), (generic_r)))))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))))))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s2 = (match (s2) with
| Some (v) -> begin
(let _179_193 = (translate_expr v var None)
in Some (_179_193))
end
| None -> begin
None
end)
in (

let c = if (is_pure_expr cond) then begin
(let _179_197 = (let _179_196 = (let _179_195 = (translate_expr_pure cond)
in (let _179_194 = (translate_expr s1 var None)
in ((_179_195), (_179_194), (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_196))
in (_179_197)::[])
end else begin
(let _179_203 = (let _179_202 = (let _179_201 = (let _179_200 = (let _179_199 = (let _179_198 = (translate_expr s1 var None)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (_179_198), (s2)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_199))
in Some (_179_200))
in (translate_expr cond (("_cond"), (None)) _179_201))
in (_179_202)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_203)
end
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_378) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_381) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (let _179_205 = (let _179_204 = (translate_type in_e.FStar_Extraction_ML_Syntax.mlty)
in Some (_179_204))
in (((Prims.fst var)), (_179_205)))
in (translate_expr in_e var stmt))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let c = if (is_pure_expr e_in) then begin
(let _179_207 = (let _179_206 = (translate_expr_pure e_in)
in (translate_match lb _179_206 var))
in (_179_207)::[])
end else begin
(

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_match_e"), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (let _179_211 = (let _179_210 = (let _179_209 = (let _179_208 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_match_e"), (None)))) var)
in Some (_179_208))
in (translate_expr e_in (("_match_e"), (None)) _179_209))
in (_179_210)::[])
in (decl_v)::_179_211))
end
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(

let c = (FStar_List.map (fun x -> (translate_expr x var None)) ls)
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let args = (create_pure_args new_fv args)
in (

let expr = (let _179_215 = (let _179_214 = (let _179_213 = (translate_arg_app e args)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_213)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_214))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_215))
in (

let c = (let _179_216 = (FStar_ST.read new_fv)
in (FStar_List.append _179_216 ((expr)::[])))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let lexpr = (create_pure_args new_fv lexpr)
in (

let expr = (match (c) with
| x when (is_prim_constructors x) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._mk_" c)), (None)))), (lexpr)))
end
| _82_426 -> begin
(let _179_225 = (let _179_224 = (FStar_List.mapi (fun i x -> (let _179_223 = (let _179_222 = (let _179_221 = (let _179_220 = (let _179_219 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_219))
in ((_179_220), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_221))
in ((_179_222), (x), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_223))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_224))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_225))
end)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr))))
in (

let c = (let _179_226 = (FStar_ST.read new_fv)
in (FStar_List.append _179_226 ((expr)::[])))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end))))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun _82_442 -> (match (_82_442) with
| (id, x) -> begin
(let _179_230 = (let _179_229 = (let _179_228 = (create_pure_args new_fv ((x)::[]))
in (FStar_List.nth _179_228 (Prims.parse_int "0")))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_229), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_230))
end)) fields)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))))))
in (

let c = (let _179_231 = (FStar_ST.read new_fv)
in (FStar_List.append _179_231 ((expr)::[])))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.mapi (fun i x -> (let _179_240 = (let _179_239 = (let _179_236 = (let _179_235 = (let _179_234 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_234))
in ((_179_235), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_236))
in (let _179_238 = (let _179_237 = (create_pure_args new_fv ((x)::[]))
in (FStar_List.nth _179_237 (Prims.parse_int "0")))
in ((_179_239), (_179_238), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_240))) lexp)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))))))
in (

let c = (let _179_241 = (FStar_ST.read new_fv)
in (FStar_List.append _179_241 ((expr)::[])))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end)))))
end
| _82_461 -> begin
(FStar_All.failwith "todo: translation ml-expr")
end))
and create_pure_args : FStar_Extraction_JavaScript_Ast.statement_t Prims.list FStar_ST.ref  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list = (fun new_fv args -> (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_469) when ((c = "Nil") || (c = "None")) -> begin
(let _179_247 = (let _179_246 = (translate_expr_pure x)
in (let _179_245 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_246), (_179_245))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_247))
end
| _82_473 -> begin
if (is_pure_expr x) then begin
(translate_expr_pure x)
end else begin
(

let fv_x = (FStar_Absyn_Util.gensym ())
in (

let _82_475 = (let _179_252 = (let _179_251 = (FStar_ST.read new_fv)
in (let _179_250 = (let _179_249 = (let _179_248 = (translate_expr x ((fv_x), (None)) None)
in (_179_248)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_249)
in (FStar_List.append _179_251 _179_250)))
in (FStar_ST.op_Colon_Equals new_fv _179_252))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None)))))
end
end)) args))
and translate_arg_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e args -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_258 = (let _179_257 = (FStar_Util.must (mk_op_bin op))
in (let _179_256 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_255 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_257), (_179_256), (_179_255)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_258))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_262 = (let _179_261 = (FStar_Util.must (mk_op_bool op))
in (let _179_260 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_259 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_261), (_179_260), (_179_259)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_262))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_266 = (let _179_265 = (let _179_263 = (mk_op_un op)
in (FStar_Util.must _179_263))
in (let _179_264 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_179_265), (_179_264))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_266))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _179_269 = (let _179_268 = (let _179_267 = (getName ((path), (function_name)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_267))
in ((_179_268), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_269))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_500) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))
end
| _82_504 -> begin
if (is_pure_expr e) then begin
(let _179_271 = (let _179_270 = (translate_expr_pure e)
in ((_179_270), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_271))
end else begin
(FStar_All.failwith "todo: translation [MLE_App]")
end
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_510) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(let _179_273 = (getName ((path), (n)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_273))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let create_fields = (FStar_List.mapi (fun i x -> (let _179_281 = (let _179_280 = (let _179_278 = (let _179_277 = (let _179_276 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_276))
in ((_179_277), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_278))
in (let _179_279 = (translate_expr_pure x)
in ((_179_280), (_179_279), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_281))) lexp)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_528 -> (match (_82_528) with
| (id, x) -> begin
(let _179_284 = (let _179_283 = (translate_expr_pure x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_283), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_284))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(match (c) with
| x when ((x = "Cons") || (x = "Nil")) -> begin
(match (lexpr) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSE_Array (None)
end
| (hd)::tl -> begin
(let _179_292 = (let _179_291 = (let _179_289 = (let _179_288 = (let _179_287 = (let _179_286 = (let _179_285 = (translate_expr_pure hd)
in (_179_285)::[])
in Some (_179_286))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_287))
in ((_179_288), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_289))
in (let _179_290 = (FStar_List.map translate_expr_pure tl)
in ((_179_291), (_179_290))))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_292))
end)
end
| x when (is_prim_constructors x) -> begin
(let _179_294 = (let _179_293 = (FStar_List.map translate_expr_pure lexpr)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._mk_" c)), (None)))), (_179_293)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_294))
end
| _82_543 -> begin
(let _179_304 = (let _179_303 = (FStar_List.mapi (fun i x -> (let _179_302 = (let _179_301 = (let _179_299 = (let _179_298 = (let _179_297 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_297))
in ((_179_298), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_299))
in (let _179_300 = (translate_expr_pure x)
in ((_179_301), (_179_300), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_302))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_303))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_304))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _82_548, _82_550) -> begin
(translate_expr_pure e)
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args = (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_562) when ((c = "Nil") || (c = "None")) -> begin
(let _179_308 = (let _179_307 = (translate_expr_pure x)
in (let _179_306 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_307), (_179_306))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_308))
end
| _82_566 -> begin
(translate_expr_pure x)
end)) args)
in (translate_arg_app e args))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, (path, name)) -> begin
(let _179_310 = (let _179_309 = (translate_expr_pure expr)
in ((_179_309), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" name)), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_310))
end
| _82_575 -> begin
(FStar_All.failwith "todo: translation ml-expr-pure")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x var -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(let _179_315 = (translate_expr expr_r var None)
in (let _179_314 = (translate_match tl fv_x var)
in (translate_pat_guard ((p), (guard)) fv_x _179_315 _179_314)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_588 fv_x s1 s2 -> (match (_82_588) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_321 = (let _179_320 = (translate_expr_pure v_guard)
in ((_179_320), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_321))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_602) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_329 = (let _179_328 = (let _179_327 = (let _179_326 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_326)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_327))
in ((_179_328), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_329))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let rec translate_p_ctor = (fun lp fv_x s1 s2 i -> (

let new_fv_x = (match (c) with
| x when (is_prim_constructors x) -> begin
(let _179_346 = (let _179_345 = (let _179_344 = (let _179_343 = (let _179_342 = (let _179_341 = (let _179_340 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_340))
in (Prims.strcat c _179_341))
in (Prims.strcat "Prims._get_" _179_342))
in ((_179_343), (None)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_344))
in ((_179_345), ((fv_x)::[])))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_346))
end
| _82_622 -> begin
(let _179_351 = (let _179_350 = (let _179_349 = (let _179_348 = (let _179_347 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_347))
in ((_179_348), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_349))
in ((fv_x), (_179_350)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_351))
end)
in (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_352 = (translate_p_ctor tl fv_x s1 s2 (i + (Prims.parse_int "1")))
in (translate_pat hd new_fv_x _179_352 s2))
end)))
in (

let if_cond = (match (c) with
| x when (is_prim_constructors x) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._is_" c)), (None)))), ((fv_x)::[])))
end
| _82_632 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
end)
in (let _179_354 = (let _179_353 = (translate_p_ctor lp fv_x s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_179_353), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_354))))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (lp) -> begin
(

let rec translate_p_branch = (fun lp fv_x s1 s2 -> (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_branch")
end
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_363 = (translate_p_branch tl fv_x s1 s2)
in (translate_pat hd fv_x s1 _179_363))
end))
in (translate_p_branch lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, lp) -> begin
(

let rec translate_p_record = (fun lp fv_x s1 s2 -> (

let new_fv_x = (fun n -> FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" n)), (None)))))))
in (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_record")
end
| (x)::[] -> begin
(translate_pat (Prims.snd x) (new_fv_x (Prims.fst x)) s1 s2)
end
| (hd)::tl -> begin
(let _179_374 = (translate_p_record tl fv_x s1 s2)
in (translate_pat (Prims.snd hd) (new_fv_x (Prims.fst hd)) _179_374 s2))
end)))
in (translate_p_record lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let rec translate_p_tuple = (fun lp d fv_x s1 s2 -> (

let new_fv_x = (let _179_389 = (let _179_388 = (let _179_387 = (let _179_386 = (let _179_385 = (FStar_Util.string_of_int d)
in (Prims.strcat "_" _179_385))
in ((_179_386), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_387))
in ((fv_x), (_179_388)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_389))
in (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_tuple")
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_390 = (translate_p_tuple tl (d + (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat hd new_fv_x _179_390 s2))
end)))
in (translate_p_tuple lp (Prims.parse_int "0") fv_x s1 s2))
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_685) -> begin
(let _179_395 = (let _179_394 = (let _179_393 = (let _179_392 = (FStar_Util.int_of_string s)
in (float_of_int _179_392))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_393))
in ((_179_394), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_395))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_691) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_696) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_704) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_397 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_397))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_711, t2) -> begin
(

let t1_t = (translate_type t1)
in (

let t2_t = (translate_type t2)
in (

let generic_t = (FStar_ST.alloc [])
in (

let addUnique = (fun lst -> (FStar_List.map (fun el -> if (not ((let _179_402 = (FStar_ST.read generic_t)
in (FStar_List.existsb (fun x -> (x = el)) _179_402)))) then begin
(let _179_404 = (let _179_403 = (FStar_ST.read generic_t)
in (FStar_List.append ((el)::[]) _179_403))
in (FStar_ST.op_Colon_Equals generic_t _179_404))
end else begin
()
end) lst))
in (

let _82_722 = (let _179_406 = (let _179_405 = (get_Generic t1_t)
in (addUnique _179_405))
in (FStar_All.pipe_right _179_406 Prims.ignore))
in (

let _82_724 = (let _179_408 = (let _179_407 = (get_Generic t2_t)
in (addUnique _179_407))
in (FStar_All.pipe_right _179_408 Prims.ignore))
in (

let generic_r = (match ((FStar_ST.read generic_t)) with
| [] -> begin
None
end
| _82_728 -> begin
(let _179_409 = (FStar_ST.read generic_t)
in Some (_179_409))
end)
in FStar_Extraction_JavaScript_Ast.JST_Function (((((((("_1"), (None))), (t1_t)))::[]), (t2_t), (generic_r))))))))))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_410 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_410)) then begin
(

let args = (FStar_List.mapi (fun i x -> (let _179_417 = (let _179_415 = (let _179_414 = (let _179_413 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_413))
in ((_179_414), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_415))
in (let _179_416 = (translate_type x)
in ((_179_417), (_179_416))))) args)
in (

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Tuple"), (""))))))::[]
in (

let arity = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_NumberLiteral ((((float_of_int (FStar_List.length args))), (""))))))::[]
in FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag (FStar_List.append arity args))), ([]), ([]))))))
end else begin
(

let args_t = (match (args) with
| [] -> begin
None
end
| _82_743 -> begin
(let _179_419 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _179_419 (fun _179_418 -> Some (_179_418))))
end)
in (let _179_422 = (let _179_421 = (let _179_420 = (getName ((path), (name)))
in FStar_Extraction_JavaScript_Ast.Unqualified (_179_420))
in ((_179_421), (args_t)))
in FStar_Extraction_JavaScript_Ast.JST_Generic (_179_422)))
end
end
end))




