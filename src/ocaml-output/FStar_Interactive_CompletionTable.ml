open Prims
let string_compare: Prims.string -> Prims.string -> Prims.int =
  fun s1  -> fun s2  -> FStar_String.compare s1 s2
type 'a heap =
  | EmptyHeap
  | Heap of ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2
let uu___is_EmptyHeap: 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | EmptyHeap  -> true | uu____41 -> false
let uu___is_Heap: 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | Heap _0 -> true | uu____66 -> false
let __proj__Heap__item___0:
  'a . 'a heap -> ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Heap _0 -> _0
let heap_merge:
  'Auu____110 .
    ('Auu____110 -> 'Auu____110 -> Prims.int) ->
      'Auu____110 heap -> 'Auu____110 heap -> 'Auu____110 heap
  =
  fun cmp  ->
    fun h1  ->
      fun h2  ->
        match (h1, h2) with
        | (EmptyHeap ,h) -> h
        | (h,EmptyHeap ) -> h
        | (Heap (v1,hh1),Heap (v2,hh2)) ->
            let uu____185 =
              let uu____186 = cmp v1 v2 in uu____186 < (Prims.parse_int "0") in
            if uu____185
            then Heap (v1, (h2 :: hh1))
            else Heap (v2, (h1 :: hh2))
let heap_insert:
  'Auu____210 .
    ('Auu____210 -> 'Auu____210 -> Prims.int) ->
      'Auu____210 heap -> 'Auu____210 -> 'Auu____210 heap
  = fun cmp  -> fun h  -> fun v1  -> heap_merge cmp (Heap (v1, [])) h
let rec heap_merge_pairs:
  'Auu____251 .
    ('Auu____251 -> 'Auu____251 -> Prims.int) ->
      'Auu____251 heap Prims.list -> 'Auu____251 heap
  =
  fun cmp  ->
    fun uu___161_271  ->
      match uu___161_271 with
      | [] -> EmptyHeap
      | h::[] -> h
      | h1::h2::hh ->
          let uu____304 = heap_merge cmp h1 h2 in
          let uu____307 = heap_merge_pairs cmp hh in
          heap_merge cmp uu____304 uu____307
let heap_peek:
  'Auu____314 .
    'Auu____314 heap -> 'Auu____314 FStar_Pervasives_Native.option
  =
  fun uu___162_322  ->
    match uu___162_322 with
    | EmptyHeap  -> FStar_Pervasives_Native.None
    | Heap (v1,uu____326) -> FStar_Pervasives_Native.Some v1
let heap_pop:
  'Auu____341 .
    ('Auu____341 -> 'Auu____341 -> Prims.int) ->
      'Auu____341 heap ->
        ('Auu____341,'Auu____341 heap) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun cmp  ->
    fun uu___163_365  ->
      match uu___163_365 with
      | EmptyHeap  -> FStar_Pervasives_Native.None
      | Heap (v1,hh) ->
          let uu____388 =
            let uu____395 = heap_merge_pairs cmp hh in (v1, uu____395) in
          FStar_Pervasives_Native.Some uu____388
let heap_from_list:
  'Auu____412 .
    ('Auu____412 -> 'Auu____412 -> Prims.int) ->
      'Auu____412 Prims.list -> 'Auu____412 heap
  =
  fun cmp  ->
    fun values  -> FStar_List.fold_left (heap_insert cmp) EmptyHeap values
let push_nodup:
  'Auu____447 .
    ('Auu____447 -> Prims.string) ->
      'Auu____447 -> 'Auu____447 Prims.list -> 'Auu____447 Prims.list
  =
  fun key_fn  ->
    fun x  ->
      fun uu___164_466  ->
        match uu___164_466 with
        | [] -> [x]
        | h::t ->
            let uu____475 =
              let uu____476 =
                let uu____477 = key_fn x in
                let uu____478 = key_fn h in
                string_compare uu____477 uu____478 in
              uu____476 = (Prims.parse_int "0") in
            if uu____475 then h :: t else x :: h :: t
let rec add_priorities:
  'Auu____490 .
    Prims.int ->
      (Prims.int,'Auu____490) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____490 Prims.list ->
          (Prims.int,'Auu____490) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun n1  ->
    fun acc  ->
      fun uu___165_516  ->
        match uu___165_516 with
        | [] -> acc
        | h::t ->
            add_priorities (n1 + (Prims.parse_int "1")) ((n1, h) :: acc) t
let merge_increasing_lists_rev:
  'a . ('a -> Prims.string) -> 'a Prims.list Prims.list -> 'a Prims.list =
  fun key_fn  ->
    fun lists  ->
      let cmp v1 v2 =
        match (v1, v2) with
        | ((uu____606,[]),uu____607) -> failwith "impossible"
        | (uu____628,(uu____629,[])) -> failwith "impossible"
        | ((pr1,h1::uu____652),(pr2,h2::uu____655)) ->
            let cmp_h =
              let uu____677 = key_fn h1 in
              let uu____678 = key_fn h2 in string_compare uu____677 uu____678 in
            if cmp_h <> (Prims.parse_int "0") then cmp_h else pr1 - pr2 in
      let rec aux lists1 acc =
        let uu____709 = heap_pop cmp lists1 in
        match uu____709 with
        | FStar_Pervasives_Native.None  -> acc
        | FStar_Pervasives_Native.Some ((pr,[]),uu____757) ->
            failwith "impossible"
        | FStar_Pervasives_Native.Some ((pr,v1::[]),lists2) ->
            let uu____847 = push_nodup key_fn v1 acc in aux lists2 uu____847
        | FStar_Pervasives_Native.Some ((pr,v1::tl1),lists2) ->
            let uu____898 = heap_insert cmp lists2 (pr, tl1) in
            let uu____915 = push_nodup key_fn v1 acc in
            aux uu____898 uu____915 in
      let lists1 = FStar_List.filter (fun x  -> x <> []) lists in
      match lists1 with
      | [] -> []
      | l::[] -> FStar_List.rev l
      | uu____942 ->
          let lists2 = add_priorities (Prims.parse_int "0") [] lists1 in
          let uu____964 = heap_from_list cmp lists2 in aux uu____964 []
type 'a btree =
  | StrEmpty
  | StrBranch of (Prims.string,'a,'a btree,'a btree)
  FStar_Pervasives_Native.tuple4
let uu___is_StrEmpty: 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrEmpty  -> true | uu____1015 -> false
let uu___is_StrBranch: 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrBranch _0 -> true | uu____1044 -> false
let __proj__StrBranch__item___0:
  'a .
    'a btree ->
      (Prims.string,'a,'a btree,'a btree) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | StrBranch _0 -> _0
let rec btree_to_list_rev:
  'Auu____1094 .
    'Auu____1094 btree ->
      (Prims.string,'Auu____1094) FStar_Pervasives_Native.tuple2 Prims.list
        ->
        (Prims.string,'Auu____1094) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun btree  ->
    fun acc  ->
      match btree with
      | StrEmpty  -> acc
      | StrBranch (key,value,lbt,rbt) ->
          let uu____1137 =
            let uu____1144 = btree_to_list_rev lbt acc in (key, value) ::
              uu____1144 in
          btree_to_list_rev rbt uu____1137
let rec btree_from_list:
  'Auu____1161 .
    (Prims.string,'Auu____1161) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        ('Auu____1161 btree,(Prims.string,'Auu____1161)
                              FStar_Pervasives_Native.tuple2 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun nodes  ->
    fun size  ->
      if size = (Prims.parse_int "0")
      then (StrEmpty, nodes)
      else
        (let lbt_size = size / (Prims.parse_int "2") in
         let rbt_size = (size - lbt_size) - (Prims.parse_int "1") in
         let uu____1205 = btree_from_list nodes lbt_size in
         match uu____1205 with
         | (lbt,nodes_left) ->
             (match nodes_left with
              | [] -> failwith "Invalid size passed to btree_from_list"
              | (k,v1)::nodes_left1 ->
                  let uu____1289 = btree_from_list nodes_left1 rbt_size in
                  (match uu____1289 with
                   | (rbt,nodes_left2) ->
                       ((StrBranch (k, v1, lbt, rbt)), nodes_left2))))
let rec btree_insert_replace: 'a . 'a btree -> Prims.string -> 'a -> 'a btree
  =
  fun bt  ->
    fun k  ->
      fun v1  ->
        match bt with
        | StrEmpty  -> StrBranch (k, v1, StrEmpty, StrEmpty)
        | StrBranch (k',v',lbt,rbt) ->
            let cmp = string_compare k k' in
            if cmp < (Prims.parse_int "0")
            then
              let uu____1390 =
                let uu____1403 = btree_insert_replace lbt k v1 in
                (k', v', uu____1403, rbt) in
              StrBranch uu____1390
            else
              if cmp > (Prims.parse_int "0")
              then
                (let uu____1413 =
                   let uu____1426 = btree_insert_replace rbt k v1 in
                   (k', v', lbt, uu____1426) in
                 StrBranch uu____1413)
              else StrBranch (k', v1, lbt, rbt)
let rec btree_find_exact:
  'a . 'a btree -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun bt  ->
    fun k  ->
      match bt with
      | StrEmpty  -> FStar_Pervasives_Native.None
      | StrBranch (k',v1,lbt,rbt) ->
          let cmp = string_compare k k' in
          if cmp < (Prims.parse_int "0")
          then btree_find_exact lbt k
          else
            if cmp > (Prims.parse_int "0")
            then btree_find_exact rbt k
            else FStar_Pervasives_Native.Some v1
let rec btree_remove: 'a . 'a btree -> Prims.string -> 'a btree =
  fun bt  ->
    fun k  ->
      match bt with
      | StrEmpty  -> StrEmpty
      | StrBranch (k',v1,lbt,rbt) ->
          let cmp = string_compare k k' in
          if cmp < (Prims.parse_int "0")
          then
            let uu____1514 =
              let uu____1527 = btree_remove lbt k in
              (k', v1, uu____1527, rbt) in
            StrBranch uu____1514
          else
            if cmp > (Prims.parse_int "0")
            then
              (let uu____1537 =
                 let uu____1550 = btree_remove rbt k in
                 (k', v1, lbt, uu____1550) in
               StrBranch uu____1537)
            else StrEmpty
type prefix_match =
  {
  prefix: Prims.string FStar_Pervasives_Native.option;
  completion: Prims.string;}
let __proj__Mkprefix_match__item__prefix:
  prefix_match -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { prefix = __fname__prefix; completion = __fname__completion;_} ->
        __fname__prefix
let __proj__Mkprefix_match__item__completion: prefix_match -> Prims.string =
  fun projectee  ->
    match projectee with
    | { prefix = __fname__prefix; completion = __fname__completion;_} ->
        __fname__completion
type path_elem = {
  imports: Prims.string Prims.list;
  segment: prefix_match;}
let __proj__Mkpath_elem__item__imports: path_elem -> Prims.string Prims.list
  =
  fun projectee  ->
    match projectee with
    | { imports = __fname__imports; segment = __fname__segment;_} ->
        __fname__imports
let __proj__Mkpath_elem__item__segment: path_elem -> prefix_match =
  fun projectee  ->
    match projectee with
    | { imports = __fname__imports; segment = __fname__segment;_} ->
        __fname__segment
let matched_prefix_of_path_elem:
  path_elem -> Prims.string FStar_Pervasives_Native.option =
  fun elem  -> (elem.segment).prefix
let mk_path_el: Prims.string Prims.list -> prefix_match -> path_elem =
  fun imports  -> fun segment  -> { imports; segment }
let rec btree_find_prefix:
  'a .
    'a btree ->
      Prims.string ->
        (prefix_match,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bt  ->
    fun prefix1  ->
      let rec aux bt1 prefix2 acc =
        match bt1 with
        | StrEmpty  -> acc
        | StrBranch (k,v1,lbt,rbt) ->
            let cmp = string_compare k prefix2 in
            let include_middle = FStar_Util.starts_with k prefix2 in
            let explore_right =
              (cmp <= (Prims.parse_int "0")) || include_middle in
            let explore_left = cmp > (Prims.parse_int "0") in
            let matches = if explore_right then aux rbt prefix2 acc else acc in
            let matches1 =
              if include_middle
              then
                ({
                   prefix = (FStar_Pervasives_Native.Some prefix2);
                   completion = k
                 }, v1)
                :: matches
              else matches in
            let matches2 =
              if explore_left then aux lbt prefix2 matches1 else matches1 in
            matches2 in
      aux bt prefix1 []
let rec btree_fold:
  'a 'b . 'a btree -> (Prims.string -> 'a -> 'b -> 'b) -> 'b -> 'b =
  fun bt  ->
    fun f  ->
      fun acc  ->
        match bt with
        | StrEmpty  -> acc
        | StrBranch (k,v1,lbt,rbt) ->
            let uu____1820 =
              let uu____1821 = btree_fold rbt f acc in f k v1 uu____1821 in
            btree_fold lbt f uu____1820
type path = path_elem Prims.list
type query = Prims.string Prims.list
let query_to_string: Prims.string Prims.list -> Prims.string =
  fun q  -> FStar_String.concat "." q
type 'a name_collection =
  | Names of 'a btree
  | ImportedNames of (Prims.string,'a name_collection Prims.list)
  FStar_Pervasives_Native.tuple2
let uu___is_Names: 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | Names _0 -> true | uu____1875 -> false
let __proj__Names__item___0: 'a . 'a name_collection -> 'a btree =
  fun projectee  -> match projectee with | Names _0 -> _0
let uu___is_ImportedNames: 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | ImportedNames _0 -> true | uu____1921 -> false
let __proj__ImportedNames__item___0:
  'a .
    'a name_collection ->
      (Prims.string,'a name_collection Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | ImportedNames _0 -> _0
type 'a names = 'a name_collection Prims.list
type 'a trie = {
  bindings: 'a names;
  namespaces: 'a trie names;}
let __proj__Mktrie__item__bindings: 'a . 'a trie -> 'a names =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; namespaces = __fname__namespaces;_} ->
        __fname__bindings
let __proj__Mktrie__item__namespaces: 'a . 'a trie -> 'a trie names =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; namespaces = __fname__namespaces;_} ->
        __fname__namespaces
let trie_empty: 'Auu____2041 . Prims.unit -> 'Auu____2041 trie =
  fun uu____2044  -> { bindings = []; namespaces = [] }
let rec names_find_exact:
  'a . 'a names -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun names1  ->
    fun ns  ->
      let uu____2075 =
        match names1 with
        | [] -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (Names bt)::names2 ->
            let uu____2125 = btree_find_exact bt ns in
            (uu____2125, (FStar_Pervasives_Native.Some names2))
        | (ImportedNames (uu____2140,names2))::more_names ->
            let uu____2157 = names_find_exact names2 ns in
            (uu____2157, (FStar_Pervasives_Native.Some more_names)) in
      match uu____2075 with
      | (result,names2) ->
          (match (result, names2) with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
              scopes) -> names_find_exact scopes ns
           | uu____2219 -> result)
let rec trie_descend_exact:
  'a . 'a trie -> query -> 'a trie FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> FStar_Pervasives_Native.Some tr
      | ns::query1 ->
          let uu____2261 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2261
            (fun scope  -> trie_descend_exact scope query1)
let names_insert: 'a . 'a names -> Prims.string -> 'a -> 'a names =
  fun name_collections  ->
    fun id  ->
      fun v1  ->
        let uu____2307 =
          match name_collections with
          | (Names bt)::tl1 -> (bt, tl1)
          | uu____2345 -> (StrEmpty, name_collections) in
        match uu____2307 with
        | (bt,name_collections1) ->
            let uu____2370 =
              let uu____2373 = btree_insert_replace bt id v1 in
              Names uu____2373 in
            uu____2370 :: name_collections1
let names_remove: 'a . 'a names -> Prims.string -> 'a names =
  fun name_collections  ->
    fun id  ->
      FStar_List.map
        (fun uu___166_2410  ->
           match uu___166_2410 with
           | Names bt ->
               let uu____2418 = btree_remove bt id in Names uu____2418
           | uu____2421 ->
               failwith "names_delete: Deleting in imported collection")
        name_collections
let rec namespaces_mutate:
  'a .
    'a trie names ->
      Prims.string ->
        query ->
          ('a trie -> 'a trie names -> 'a trie) ->
            ('a trie -> 'a trie) -> 'a trie names
  =
  fun namespaces  ->
    fun ns  ->
      fun query  ->
        fun mut_node  ->
          fun mut_leaf  ->
            let trie =
              let uu____2558 = names_find_exact namespaces ns in
              FStar_Util.dflt (trie_empty ()) uu____2558 in
            let uu____2569 = trie_mutate trie query mut_node mut_leaf in
            names_insert namespaces ns uu____2569
and trie_mutate:
  'a .
    'a trie ->
      query ->
        ('a trie -> 'a trie names -> 'a trie) ->
          ('a trie -> 'a trie) -> 'a trie
  =
  fun tr  ->
    fun query  ->
      fun mut_node  ->
        fun mut_leaf  ->
          match query with
          | [] -> mut_leaf tr
          | id::query1 ->
              let uu____2605 =
                namespaces_mutate tr.namespaces id query1 mut_node mut_leaf in
              mut_node tr uu____2605
let trie_mutate_leaf:
  'a . 'a trie -> query -> ('a trie -> 'a trie) -> 'a trie =
  fun tr  ->
    fun query  ->
      trie_mutate tr query
        (fun tr1  ->
           fun namespaces  ->
             let uu___168_2655 = tr1 in
             { bindings = (uu___168_2655.bindings); namespaces })
let trie_insert: 'a . 'a trie -> query -> Prims.string -> 'a -> 'a trie =
  fun tr  ->
    fun ns_query  ->
      fun id  ->
        fun v1  ->
          trie_mutate_leaf tr ns_query
            (fun tr1  ->
               let uu___169_2699 = tr1 in
               let uu____2702 = names_insert tr1.bindings id v1 in
               {
                 bindings = uu____2702;
                 namespaces = (uu___169_2699.namespaces)
               })
let trie_import:
  'a .
    'a trie ->
      query ->
        query -> ('a trie -> 'a trie -> Prims.string -> 'a trie) -> 'a trie
  =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        fun mutator  ->
          let label = query_to_string included_query in
          let included_trie =
            let uu____2771 = trie_descend_exact tr included_query in
            FStar_Util.dflt (trie_empty ()) uu____2771 in
          trie_mutate_leaf tr host_query
            (fun tr1  -> mutator tr1 included_trie label)
let trie_include: 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___170_2820 = tr1 in
                 {
                   bindings = ((ImportedNames (label, (inc.bindings))) ::
                     (tr1.bindings));
                   namespaces = (uu___170_2820.namespaces)
                 })
let trie_open_namespace: 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___171_2865 = tr1 in
                 {
                   bindings = (uu___171_2865.bindings);
                   namespaces = ((ImportedNames (label, (inc.namespaces))) ::
                     (tr1.namespaces))
                 })
let trie_add_alias: 'a . 'a trie -> Prims.string -> query -> query -> 'a trie
  =
  fun tr  ->
    fun key  ->
      fun host_query  ->
        fun included_query  ->
          trie_import tr host_query included_query
            (fun tr1  ->
               fun inc  ->
                 fun label  ->
                   trie_mutate_leaf tr1 [key]
                     (fun _ignored_overwritten_trie  ->
                        {
                          bindings = [ImportedNames (label, (inc.bindings))];
                          namespaces = []
                        }))
let names_revmap:
  'a 'b .
    ('a btree -> 'b) ->
      'a names ->
        (Prims.string Prims.list,'b) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun fn  ->
    fun name_collections  ->
      let rec aux acc imports name_collections1 =
        FStar_List.fold_left
          (fun acc1  ->
             fun uu___167_3043  ->
               match uu___167_3043 with
               | Names bt ->
                   let uu____3065 =
                     let uu____3072 = fn bt in (imports, uu____3072) in
                   uu____3065 :: acc1
               | ImportedNames (nm,name_collections2) ->
                   aux acc1 (nm :: imports) name_collections2) acc
          name_collections1 in
      aux [] [] name_collections
let btree_find_all:
  'a .
    Prims.string FStar_Pervasives_Native.option ->
      'a btree -> (prefix_match,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun prefix1  ->
    fun bt  ->
      btree_fold bt
        (fun k  ->
           fun tr  ->
             fun acc  -> ({ prefix = prefix1; completion = k }, tr) :: acc)
        []
type name_search_term =
  | NSTAll
  | NSTNone
  | NSTPrefix of Prims.string
let uu___is_NSTAll: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTAll  -> true | uu____3164 -> false
let uu___is_NSTNone: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTNone  -> true | uu____3169 -> false
let uu___is_NSTPrefix: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTPrefix _0 -> true | uu____3175 -> false
let __proj__NSTPrefix__item___0: name_search_term -> Prims.string =
  fun projectee  -> match projectee with | NSTPrefix _0 -> _0
let names_find_rev:
  'a .
    'a names ->
      name_search_term ->
        (path_elem,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun names1  ->
    fun id  ->
      let matching_values_per_collection_with_imports =
        match id with
        | NSTNone  -> []
        | NSTAll  ->
            names_revmap (btree_find_all FStar_Pervasives_Native.None) names1
        | NSTPrefix "" ->
            names_revmap (btree_find_all (FStar_Pervasives_Native.Some ""))
              names1
        | NSTPrefix id1 ->
            names_revmap (fun bt  -> btree_find_prefix bt id1) names1 in
      let matching_values_per_collection =
        FStar_List.map
          (fun uu____3312  ->
             match uu____3312 with
             | (imports,matches) ->
                 FStar_List.map
                   (fun uu____3360  ->
                      match uu____3360 with
                      | (segment,v1) -> ((mk_path_el imports segment), v1))
                   matches) matching_values_per_collection_with_imports in
      merge_increasing_lists_rev
        (fun uu____3378  ->
           match uu____3378 with
           | (path_el,uu____3384) -> (path_el.segment).completion)
        matching_values_per_collection
let rec trie_find_prefix':
  'a .
    'a trie ->
      path ->
        query ->
          (path,'a) FStar_Pervasives_Native.tuple2 Prims.list ->
            (path,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun tr  ->
    fun path_acc  ->
      fun query  ->
        fun acc  ->
          let uu____3434 =
            match query with
            | [] -> (NSTAll, NSTAll, [])
            | id::[] -> ((NSTPrefix id), (NSTPrefix id), [])
            | ns::query1 -> ((NSTPrefix ns), NSTNone, query1) in
          match uu____3434 with
          | (ns_search_term,bindings_search_term,query1) ->
              let matching_namespaces_rev =
                names_find_rev tr.namespaces ns_search_term in
              let acc_with_recursive_bindings =
                FStar_List.fold_left
                  (fun acc1  ->
                     fun uu____3510  ->
                       match uu____3510 with
                       | (path_el,trie) ->
                           trie_find_prefix' trie (path_el :: path_acc)
                             query1 acc1) acc matching_namespaces_rev in
              let matching_bindings_rev =
                names_find_rev tr.bindings bindings_search_term in
              FStar_List.rev_map_onto
                (fun uu____3555  ->
                   match uu____3555 with
                   | (path_el,v1) ->
                       ((FStar_List.rev (path_el :: path_acc)), v1))
                matching_bindings_rev acc_with_recursive_bindings
let trie_find_prefix:
  'a .
    'a trie -> query -> (path,'a) FStar_Pervasives_Native.tuple2 Prims.list
  = fun tr  -> fun query  -> trie_find_prefix' tr [] query []
type symbol =
  | Module of Prims.bool
  | Namespace of Prims.bool
  | Lid of FStar_Ident.lid
let uu___is_Module: symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____3616 -> false
let __proj__Module__item___0: symbol -> Prims.bool =
  fun projectee  -> match projectee with | Module _0 -> _0
let uu___is_Namespace: symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____3630 -> false
let __proj__Namespace__item___0: symbol -> Prims.bool =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Lid: symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Lid _0 -> true | uu____3644 -> false
let __proj__Lid__item___0: symbol -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Lid _0 -> _0
type table = symbol trie
let empty: table = trie_empty ()
let insert: table -> query -> Prims.string -> symbol -> table =
  fun tbl  ->
    fun host_query  -> fun id  -> fun c  -> trie_insert tbl host_query id c
let register_alias: table -> Prims.string -> query -> query -> table =
  fun tbl  ->
    fun key  ->
      fun host_query  ->
        fun included_query  ->
          trie_add_alias tbl key host_query included_query
let register_include: table -> query -> query -> table =
  fun tbl  ->
    fun host_query  ->
      fun included_query  -> trie_include tbl host_query included_query
let register_open: table -> Prims.bool -> query -> query -> table =
  fun tbl  ->
    fun is_module  ->
      fun host_query  ->
        fun included_query  ->
          if is_module
          then trie_include tbl host_query included_query
          else trie_open_namespace tbl host_query included_query
let module_marker: Prims.string = "${id}"
let namespace_marker: Prims.string = "(${...})"
let register_module_path: table -> Prims.bool -> query -> table =
  fun tbl  ->
    fun loaded  ->
      fun mod_query  ->
        let ins_ns bindings loaded1 =
          let uu____3744 = names_find_exact bindings module_marker in
          match uu____3744 with
          | FStar_Pervasives_Native.Some (Module uu____3751) -> bindings
          | FStar_Pervasives_Native.Some uu____3753 ->
              failwith "ins_ns: namespace or lid under module key"
          | FStar_Pervasives_Native.None  ->
              let uu____3756 =
                let uu____3763 = names_find_exact bindings namespace_marker in
                (uu____3763, loaded1) in
              (match uu____3756 with
               | (FStar_Pervasives_Native.None ,uu____3772) ->
                   names_insert bindings namespace_marker (Namespace loaded1)
               | (FStar_Pervasives_Native.Some (Namespace (false )),true ) ->
                   names_insert bindings namespace_marker (Namespace loaded1)
               | (FStar_Pervasives_Native.Some uu____3781,uu____3782) ->
                   bindings) in
        let ins_mod bindings loaded1 =
          let bindings1 = names_remove bindings namespace_marker in
          names_insert bindings1 module_marker (Module loaded1) in
        trie_mutate tbl mod_query
          (fun tr  ->
             fun namespaces  ->
               let uu___173_3822 = tr in
               let uu____3825 = ins_ns tr.bindings loaded in
               { bindings = uu____3825; namespaces })
          (fun tr  ->
             let uu___172_3839 = tr in
             let uu____3842 = ins_mod tr.bindings loaded in
             { bindings = uu____3842; namespaces = (uu___172_3839.namespaces)
             })
let string_of_path: path -> Prims.string =
  fun path  ->
    let uu____3852 = FStar_List.map (fun el  -> (el.segment).completion) path in
    FStar_String.concat "." uu____3852
let match_length_of_path: path -> Prims.int =
  fun path  ->
    let uu____3861 =
      FStar_List.fold_left
        (fun acc  ->
           fun elem  ->
             let uu____3895 = acc in
             match uu____3895 with
             | (acc_len,uu____3913) ->
                 (match (elem.segment).prefix with
                  | FStar_Pervasives_Native.Some prefix1 ->
                      let completion_len =
                        FStar_String.length (elem.segment).completion in
                      (((acc_len + (Prims.parse_int "1")) + completion_len),
                        (prefix1, completion_len))
                  | FStar_Pervasives_Native.None  -> acc))
        ((Prims.parse_int "0"), ("", (Prims.parse_int "0"))) path in
    match uu____3861 with
    | (length1,(last_prefix,last_completion_length)) ->
        ((length1 - (Prims.parse_int "1")) - last_completion_length) +
          (FStar_String.length last_prefix)
let first_import_of_path: path -> Prims.string FStar_Pervasives_Native.option
  =
  fun path  ->
    match path with
    | [] -> FStar_Pervasives_Native.None
    | { imports; segment = uu____3968;_}::uu____3969 ->
        FStar_List.last imports
type completion_result =
  {
  completion_match_length: Prims.int;
  completion_candidate: Prims.string;
  completion_annotation: Prims.string;}
let __proj__Mkcompletion_result__item__completion_match_length:
  completion_result -> Prims.int =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_match_length
let __proj__Mkcompletion_result__item__completion_candidate:
  completion_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_candidate
let __proj__Mkcompletion_result__item__completion_annotation:
  completion_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_annotation
let json_of_completion_result: completion_result -> FStar_Util.json =
  fun result  ->
    FStar_Util.JsonList
      [FStar_Util.JsonInt (result.completion_match_length);
      FStar_Util.JsonStr (result.completion_annotation);
      FStar_Util.JsonStr (result.completion_candidate)]
let completion_result_of_lid:
  'Auu____4017 . 'Auu____4017 -> path -> completion_result =
  fun _lid  ->
    fun path  ->
      let uu____4026 = match_length_of_path path in
      let uu____4027 = string_of_path path in
      let uu____4028 =
        let uu____4029 = first_import_of_path path in
        FStar_Util.dflt "" uu____4029 in
      {
        completion_match_length = uu____4026;
        completion_candidate = uu____4027;
        completion_annotation = uu____4028
      }
let completion_result_of_mod:
  Prims.string -> Prims.bool -> path -> completion_result =
  fun annot  ->
    fun loaded  ->
      fun path  ->
        let uu____4044 = match_length_of_path path in
        let uu____4045 = string_of_path path in
        {
          completion_match_length = uu____4044;
          completion_candidate = uu____4045;
          completion_annotation =
            (Prims.strcat annot (if loaded then "+" else "-"))
        }
let completion_result_of_path_and_symb:
  (path,symbol) FStar_Pervasives_Native.tuple2 -> completion_result =
  fun uu____4054  ->
    match uu____4054 with
    | (path,symb) ->
        (match symb with
         | Lid l -> completion_result_of_lid l path
         | Module loaded -> completion_result_of_mod "mod" loaded path
         | Namespace loaded -> completion_result_of_mod "ns" loaded path)
let incorrect_result: path -> symbol -> Prims.bool =
  fun path  ->
    fun symbol  ->
      match symbol with
      | Module uu____4072 ->
          let uu____4073 = first_import_of_path path in
          (match uu____4073 with
           | FStar_Pervasives_Native.Some uu____4076 -> true
           | FStar_Pervasives_Native.None  -> false)
      | Namespace uu____4077 ->
          let uu____4078 = first_import_of_path path in
          (match uu____4078 with
           | FStar_Pervasives_Native.Some uu____4081 -> true
           | FStar_Pervasives_Native.None  -> false)
      | uu____4082 -> false
let autocomplete:
  table ->
    query ->
      (path ->
         symbol ->
           (path,symbol) FStar_Pervasives_Native.tuple2
             FStar_Pervasives_Native.option)
        -> completion_result Prims.list
  =
  fun tbl  ->
    fun query  ->
      fun filter1  ->
        let uu____4119 = trie_find_prefix tbl query in
        FStar_List.filter_map
          (fun uu____4134  ->
             match uu____4134 with
             | (path,symbol) ->
                 let uu____4143 = incorrect_result path symbol in
                 if uu____4143
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____4147 = filter1 path symbol in
                    FStar_Util.map_option completion_result_of_path_and_symb
                      uu____4147)) uu____4119