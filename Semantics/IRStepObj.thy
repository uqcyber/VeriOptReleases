section \<open>Control-flow Semantics\<close>

theory IRStepObj
  imports
    TreeToGraph
    Graph.Class
begin

subsection \<open>Object Heap\<close>

text \<open>
The heap model we introduce maps field references to object instances to runtime values.
We use the H[f][p] heap representation. See @{text "\\cite{heap-reps-2011}"}.

We also introduce the DynamicHeap type which allocates new object references sequentially
storing the next free object reference as 'Free'.
\<close>
(* TODO: Record volatile fields?  Include class name of field? *)
text_raw \<open>\Snip{heapdef}%\<close>
type_synonym ('a, 'b) Heap = "'a \<Rightarrow> 'b \<Rightarrow> Value"
type_synonym Free = "nat"
type_synonym ('a, 'b) DynamicHeap = "('a, 'b) Heap \<times> Free"

fun h_load_field :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) DynamicHeap \<Rightarrow> Value" where
  "h_load_field f r (h, n) = h f r"

fun h_store_field :: "'a \<Rightarrow> 'b \<Rightarrow> Value \<Rightarrow> ('a, 'b) DynamicHeap \<Rightarrow> ('a, 'b) DynamicHeap" where
  "h_store_field f r v (h, n) = (h(f := ((h f)(r := v))), n)"

(* Alternatively store classname in ObjRef ? *)
fun h_new_inst :: "(string, objref) DynamicHeap \<Rightarrow> string \<Rightarrow> (string, objref) DynamicHeap \<times> Value" where
  "h_new_inst (h, n) className = (h_store_field ''class'' (Some n) (ObjStr className) (h,n+1), (ObjRef (Some n)))"

type_synonym FieldRefHeap = "(string, objref) DynamicHeap"
text_raw \<open>\EndSnip\<close>

definition new_heap :: "('a, 'b) DynamicHeap" where
  "new_heap =  ((\<lambda>f. \<lambda>p. UndefVal), 0)"

subsection \<open>Intraprocedural Semantics\<close>

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

inductive indexof :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "find_index x xs = i \<Longrightarrow> indexof xs i x"

lemma indexof_det:
  "indexof xs i x \<Longrightarrow> indexof xs i' x \<Longrightarrow> i = i'"
  apply (induction rule: indexof.induct)
  by (simp add: indexof.simps)

code_pred (modes: i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool) indexof .

notation (latex output)
  indexof ("_!_ = _")

fun phi_list :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g n = 
    (filter (\<lambda>x.(is_PhiNode (kind g x)))
      (sorted_list_of_set (usages g n)))"

(* TODO this produces two parse trees after importing Class *)

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (n # ns) (v # vs) m = (set_phis ns vs (m(n := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # ns) [] m = m"

definition
  fun_add :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" (infixl "++\<^sub>f" 100) where
  "f1 ++\<^sub>f f2 = (\<lambda>x. case f2 x of None \<Rightarrow> f1 x | Some y \<Rightarrow> y)"

definition upds :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow> 'b)" ("_/'(_ [\<rightarrow>] _/')" 900) where
  "upds m ns vs = m ++\<^sub>f (map_of (rev (zip ns vs)))"

lemma fun_add_empty:
  "xs ++\<^sub>f (map_of []) = xs"
  unfolding fun_add_def by simp

lemma upds_inc:
  "m(a#as [\<rightarrow>] b#bs) = ((m(a:=b))(as[\<rightarrow>]bs))"
  unfolding upds_def fun_add_def apply auto
  unfolding fun_upd_def map_add_def
proof -
  have "\<forall>aa. (case case map_of (rev (zip as bs)) aa of None \<Rightarrow> if aa = a then Some b else None | Some x \<Rightarrow> Some x of None \<Rightarrow> m aa | Some b \<Rightarrow> b) = (case map_of (rev (zip as bs)) aa of None \<Rightarrow> if aa = a then b else m aa | Some b \<Rightarrow> b)"
    by (smt (z3) option.case_eq_if option.simps(5))
  then show "(\<lambda>aa. case case map_of (rev (zip as bs)) aa of None \<Rightarrow> if aa = a then Some b else None | Some x \<Rightarrow> Some x of None \<Rightarrow> m aa | Some b \<Rightarrow> b) = (\<lambda>aa. case map_of (rev (zip as bs)) aa of None \<Rightarrow> if aa = a then b else m aa | Some b \<Rightarrow> b)"
    by presburger
qed

lemma upds_compose:
  "a ++\<^sub>f map_of (rev (zip (n # ns) (v # vs))) = a(n := v) ++\<^sub>f map_of (rev (zip ns vs))"
  using upds_inc
  by (metis upds_def)

lemma "set_phis ns vs = (\<lambda>m. upds m ns vs)"
proof (induction rule: set_phis.induct)
  case (1 m)
  then show ?case unfolding set_phis.simps upds_def
    by (metis Nil_eq_zip_iff Nil_is_rev_conv fun_add_empty)
next
  case (2 n xs v vs m)
  then show ?case unfolding set_phis.simps upds_def
    by (metis upds_compose)
next
  case (3 v vs m)
  then show ?case
    by (metis fun_add_empty rev.simps(1) upds_def set_phis.simps(3) zip_Nil)
next
  case (4 x xs m)
  then show ?case
    by (metis Nil_eq_zip_iff fun_add_empty rev.simps(1) upds_def set_phis.simps(4))
qed

fun is_PhiKind :: "IRGraph \<Rightarrow> ID \<Rightarrow> bool" where
  "is_PhiKind g nid = is_PhiNode (kind g nid)"

definition filter_phis :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "filter_phis g merge = (filter (is_PhiKind g) (sorted_list_of_set (usages g merge)))"

definition phi_inputs :: "IRGraph \<Rightarrow> ID list \<Rightarrow> nat \<Rightarrow> ID list" where
  "phi_inputs g phis i = (map (\<lambda>n. (inputs_of (kind g n))!(i + 1)) phis)"


text \<open>
Intraprocedural semantics are given as a small-step semantics.

Within the context of a graph, the configuration triple, (ID, MethodState, Heap),
is related to the subsequent configuration.
\<close>

inductive step :: "IRGraph \<Rightarrow> Params \<Rightarrow> (ID \<times> MapState \<times> FieldRefHeap) \<Rightarrow> (ID \<times> MapState \<times> FieldRefHeap) \<Rightarrow> bool"
  ("_, _ \<turnstile> _ \<rightarrow> _" 55) for g p where

(* TODO this produces two parse trees after importing Class *)
  SequentialNode:
  "\<lbrakk>is_sequential_node (kind g nid);
    nid' = (successors_of (kind g nid))!0\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)" |

(* TODO condition before FixedGuard is IsNullNode, so FixedGuard only proceeds if this is *false*.
        If any input to a FixedGuard evaluates to True when it's safe to proceed, this 
        implementation won't work *)
  FixedGuardNode:
   "\<lbrakk>(kind g nid) = (FixedGuardNode cond before next);
     [g, m, p] \<turnstile> cond \<mapsto> val;

     \<not>(val_to_bool val)\<rbrakk> 
     \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |

   BytecodeExceptionNode:
  "\<lbrakk>(kind g nid) = (BytecodeExceptionNode args st nid');
    exceptionType = stp_type (stamp g nid);
    (h', ref) = h_new_inst h exceptionType;
    m' = m(nid := ref)\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')" |

  IfNode:
  "\<lbrakk>kind g nid = (IfNode cond tb fb);
    [g, m, p] \<turnstile> cond \<mapsto> val;
    nid' = (if val_to_bool val then tb else fb)\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)" |  

  EndNodes:
  "\<lbrakk>is_AbstractEndNode (kind g nid);
    merge = any_usage g nid;
    is_AbstractMergeNode (kind g merge);

    indexof (inputs_of (kind g merge)) i nid;
    phis = filter_phis g merge;
    inps = phi_inputs g phis i;
    [g, m, p] \<turnstile> inps [\<mapsto>] vs;

    m' = (m(phis[\<rightarrow>]vs))\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (merge, m', h)" |

  NewArrayNode:
    "\<lbrakk>kind g nid = (NewArrayNode len st nid');
      [g, m, p] \<turnstile> len \<mapsto> length';

      arrayType = stp_type (stamp g nid);
      (h', ref) = h_new_inst h arrayType;
      ref = ObjRef refNo;
      h'' = h_store_field '''' refNo (intval_new_array length' arrayType) h';

      m' = m(nid := ref)\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'')" |

  ArrayLengthNode:
    "\<lbrakk>kind g nid = (ArrayLengthNode x nid');
      [g, m, p] \<turnstile> x \<mapsto> ObjRef ref;

      h_load_field '''' ref h = arrayVal;
      length' = array_length (arrayVal);

      m' = m(nid := length')\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h)" |

  LoadIndexedNode:
    "\<lbrakk>kind g nid = (LoadIndexedNode index guard array nid');
      [g, m, p] \<turnstile> index \<mapsto> indexVal;
      [g, m, p] \<turnstile> array \<mapsto> ObjRef ref;

      h_load_field '''' ref h = arrayVal;
      loaded = intval_load_index arrayVal indexVal;

      m' = m(nid := loaded)\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h)" |

  StoreIndexedNode:
    "\<lbrakk>kind g nid = (StoreIndexedNode check val st index guard array nid');
      [g, m, p] \<turnstile> index \<mapsto> indexVal;
      [g, m, p] \<turnstile> array \<mapsto> ObjRef ref;
      [g, m, p] \<turnstile> val \<mapsto> value;

      h_load_field '''' ref h = arrayVal;
      updated = intval_store_index arrayVal indexVal value;
      h' = h_store_field '''' ref updated h;
      m' =  m(nid := updated)\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')" |

  NewInstanceNode:
    "\<lbrakk>kind g nid = (NewInstanceNode nid cname obj nid');
      (h', ref) = h_new_inst h cname; 
      m' = m(nid := ref)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')" |

  LoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode nid f (Some obj) nid');
      [g, m, p] \<turnstile> obj \<mapsto> ObjRef ref;
      m' = m(nid := h_load_field f ref h)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h)" |

  SignedDivNode:
    "\<lbrakk>kind g nid = (SignedDivNode nid x y zero sb next);
      [g, m, p] \<turnstile> x \<mapsto> v1;
      [g, m, p] \<turnstile> y \<mapsto> v2;
      m' =  m(nid := intval_div v1 v2)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (next, m', h)" |

  SignedRemNode:
    "\<lbrakk>kind g nid = (SignedRemNode nid x y zero sb next);
      [g, m, p] \<turnstile> x \<mapsto> v1;
      [g, m, p] \<turnstile> y \<mapsto> v2;
      m' =  m(nid := intval_mod v1 v2)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (next, m', h)" |

  StaticLoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode nid f None nid');
      m' =  m(nid := h_load_field f None h)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h)" |

  StoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f newval _ (Some obj) nid');
      [g, m, p] \<turnstile> newval \<mapsto> val;
      [g, m, p] \<turnstile> obj \<mapsto> ObjRef ref;
      h' = h_store_field f ref val h;
      m' =  m(nid := val)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')" |

  StaticStoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f newval _ None nid');
      [g, m, p] \<turnstile> newval \<mapsto> val;
      h' = h_store_field f None val h;
      m' =  m(nid := val)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i * i * i \<Rightarrow> o * o * o \<Rightarrow> bool) step .

subsection \<open>Interprocedural Semantics\<close>

type_synonym Signature = "string"
type_synonym Program = "Signature \<rightharpoonup> IRGraph"
type_synonym System = "Program \<times> Classes"

(* Performs a dynamic look-up in the list of instantiated classes to retrieve the appropriate 
   IRGraph to run. Takes: 
    - A System containing the Program and list of classes.
    - The fully-qualified name (dynamic type) of the object which the method has been invoked on.
    - The fully-qualified name of the method invoked. 
    - The path from the object the method was invoked on to java.lang.Object.
 *)
function dynamic_lookup :: "System \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> IRGraph option" where
  "dynamic_lookup (P,cl) cn mn path = (
      if (cn = ''None'' \<or> cn \<notin> set (Class.mapJVMFunc class_name cl) \<or> path = [])
        then (P mn)
        else (
              
              let method_index = (find_index (get_simple_signature mn) (CLsimple_signatures cn cl)) in
              let parent = hd path in

          if (method_index = length (CLsimple_signatures cn cl))
            then (dynamic_lookup (P, cl) parent mn (tl path))
            else (P (nth (map method_unique_name (CLget_Methods cn cl)) method_index))
        )
      )
  "
  by auto
termination dynamic_lookup apply (relation "measure (\<lambda>(S,cn,mn,path). (length path))") by auto

inductive step_top :: "System \<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> Params) list \<times> FieldRefHeap \<Rightarrow> 
                                 (IRGraph \<times> ID \<times> MapState \<times> Params) list \<times> FieldRefHeap \<Rightarrow> bool"
  ("_ \<turnstile> _ \<longrightarrow> _" 55) 
  for S where

  Lift:
  "\<lbrakk>g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')\<rbrakk> 
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#stk, h) \<longrightarrow> ((g,nid',m',p)#stk, h')" |

 InvokeNodeStepStatic:
  "\<lbrakk>is_Invoke (kind g nid);
    callTarget = ir_callTarget (kind g nid);
    kind g callTarget = (MethodCallTargetNode targetMethod actuals invoke_kind);
    \<not>(hasReceiver invoke_kind);
    Some targetGraph = (dynamic_lookup S ''None'' targetMethod []);
    [g, m, p] \<turnstile> actuals [\<mapsto>] p'\<rbrakk>
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#stk, h) \<longrightarrow> ((targetGraph,0,new_map_state,p')#(g,nid,m,p)#stk, h)" |

  InvokeNodeStep:
  "\<lbrakk>is_Invoke (kind g nid);
    callTarget = ir_callTarget (kind g nid);
    kind g callTarget = (MethodCallTargetNode targetMethod arguments invoke_kind);
    hasReceiver invoke_kind; 
    [g, m, p] \<turnstile> arguments [\<mapsto>] p';
    ObjRef self = hd p';
    ObjStr cname = (h_load_field ''class'' self h);
    S = (P,cl);
    Some targetGraph = dynamic_lookup S cname targetMethod (class_parents (CLget_JVMClass cname cl))\<rbrakk>
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#stk, h) \<longrightarrow> ((targetGraph,0,new_map_state,p')#(g,nid,m,p)#stk, h)" |

(* TODO this produces two parse trees after importing Class *)
  ReturnNode:
  "\<lbrakk>kind g nid = (ReturnNode (Some expr) _);
    [g, m, p] \<turnstile> expr \<mapsto> v;

    m'\<^sub>c = m\<^sub>c(nid\<^sub>c := v);
    nid'\<^sub>c = (successors_of (kind g\<^sub>c nid\<^sub>c))!0\<rbrakk> 
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#(g\<^sub>c,nid\<^sub>c,m\<^sub>c,p\<^sub>c)#stk, h) \<longrightarrow> ((g\<^sub>c,nid'\<^sub>c,m'\<^sub>c,p\<^sub>c)#stk, h)" |

(* TODO this produces two parse trees after importing Class *)
  ReturnNodeVoid:
  "\<lbrakk>kind g nid = (ReturnNode None _);
    
    nid'\<^sub>c = (successors_of (kind g\<^sub>c nid\<^sub>c))!0\<rbrakk> 
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#(g\<^sub>c,nid\<^sub>c,m\<^sub>c,p\<^sub>c)#stk, h) \<longrightarrow> ((g\<^sub>c,nid'\<^sub>c,m\<^sub>c,p\<^sub>c)#stk, h)" |

  UnwindNode:
  "\<lbrakk>kind g nid = (UnwindNode exception);

    [g, m, p] \<turnstile> exception \<mapsto> e;
     
    kind g\<^sub>c nid\<^sub>c = (InvokeWithExceptionNode _ _ _ _ _ _ exEdge);

    m'\<^sub>c = m\<^sub>c(nid\<^sub>c := e)\<rbrakk>
  \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#(g\<^sub>c,nid\<^sub>c,m\<^sub>c,p\<^sub>c)#stk, h) \<longrightarrow> ((g\<^sub>c,exEdge,m'\<^sub>c,p\<^sub>c)#stk, h)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) step_top .

subsection \<open>Big-step Execution\<close>

type_synonym Trace = "(IRGraph \<times> ID \<times> MapState \<times> Params) list"

fun has_return :: "MapState \<Rightarrow> bool" where
  "has_return m = (m 0 \<noteq> UndefVal)"

inductive exec :: "System 
      \<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> Params) list \<times> FieldRefHeap
      \<Rightarrow> Trace 
      \<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> Params) list \<times> FieldRefHeap
      \<Rightarrow> Trace 
      \<Rightarrow> bool"
  ("_ \<turnstile> _ | _ \<longrightarrow>* _ | _")
  for P where
  "\<lbrakk>P \<turnstile> (((g,nid,m,p)#xs),h) \<longrightarrow> (((g',nid',m',p')#ys),h');
    \<not>(has_return m');

    l' = (l @ [(g,nid,m,p)]);

    exec P (((g',nid',m',p')#ys),h') l' next_state l''\<rbrakk> 
    \<Longrightarrow> exec P (((g,nid,m,p)#xs),h) l next_state l''" 
(* TODO: refactor this stopping condition to be more abstract *)
  |
  "\<lbrakk>P \<turnstile> (((g,nid,m,p)#xs),h) \<longrightarrow> (((g',nid',m',p')#ys),h');
    has_return m';

    l' = (l @ [(g,nid,m,p)])\<rbrakk>
    \<Longrightarrow> exec P (((g,nid,m,p)#xs),h) l (((g',nid',m',p')#ys),h') l'"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as Exec) "exec" .

inductive exec_debug :: "System
     \<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> Params) list \<times> FieldRefHeap
     \<Rightarrow> nat
     \<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> Params) list \<times> FieldRefHeap
     \<Rightarrow> bool"
  ("_\<turnstile>_\<rightarrow>*_* _")
  where
  "\<lbrakk>n > 0;
    p \<turnstile> s \<longrightarrow> s';
    exec_debug p s' (n - 1) s''\<rbrakk> 
    \<Longrightarrow> exec_debug p s n s''" |

  "\<lbrakk>n = 0\<rbrakk>
    \<Longrightarrow> exec_debug p s n s"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) "exec_debug" .

subsubsection \<open>Heap Testing\<close>

definition p3:: Params where
  "p3 = [IntVal 32 3]"

fun graphToSystem :: "IRGraph \<Rightarrow> System" where
  "graphToSystem graph = ((\<lambda>x. Some graph), JVMClasses [])"

(* Eg. call eg2_sq with [3] \<longrightarrow> 9 *)
values "{(prod.fst(prod.snd (prod.snd (hd (prod.fst res))))) 0 
        | res. (graphToSystem eg2_sq) \<turnstile> ([(eg2_sq,0,new_map_state,p3), (eg2_sq,0,new_map_state,p3)], new_heap) \<rightarrow>*2* res}"

definition field_sq :: string where
  "field_sq = ''sq''"

definition eg3_sq :: IRGraph where
  "eg3_sq = irgraph [
    (0, StartNode None 4, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (3, MulNode 1 1, default_stamp),
    (4, StoreFieldNode 4 field_sq 3 None None 5, VoidStamp),
    (5, ReturnNode (Some 3) None, default_stamp)
   ]"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object None={sq: 9} *)
values "{h_load_field field_sq None (prod.snd res)
        | res. (graphToSystem eg3_sq) \<turnstile> ([(eg3_sq, 0, new_map_state, p3), (eg3_sq, 0, new_map_state, p3)], new_heap) \<rightarrow>*3* res}"

definition eg4_sq :: IRGraph where
  "eg4_sq = irgraph [
    (0, StartNode None 4, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (3, MulNode 1 1, default_stamp),
    (4, NewInstanceNode 4 ''obj_class'' None 5, ObjectStamp ''obj_class'' True True False),
    (5, StoreFieldNode 5 field_sq 3 None (Some 4) 6, VoidStamp),
    (6, ReturnNode (Some 3) None, default_stamp)
   ]"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object 0={sq: 9} *)
values "{h_load_field field_sq (Some 0) (prod.snd res) 
        | res. (graphToSystem (eg4_sq)) \<turnstile> ([(eg4_sq, 0, new_map_state, p3), (eg4_sq, 0, new_map_state, p3)], new_heap) \<rightarrow>*3* res}"

end