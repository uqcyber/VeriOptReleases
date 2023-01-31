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

fun phi_list :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g n = 
    (filter (\<lambda>x.(is_PhiNode (kind g x)))
      (sorted_list_of_set (usages g n)))"

fun input_index :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (inputs_of (kind g n))"

(* TODO this produces two parse trees after importing Class *)
fun phi_inputs :: "IRGraph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inputs_of (kind g n))!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (n # xs) (v # vs) m = (set_phis xs vs (m(n := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"


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

  IfNode:
  "\<lbrakk>kind g nid = (IfNode cond tb fb);
    g \<turnstile> cond \<simeq> condE; 
    [m, p] \<turnstile> condE \<mapsto> val;
    nid' = (if val_to_bool val then tb else fb)\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)" |  

  EndNodes:
  "\<lbrakk>is_AbstractEndNode (kind g nid);
    merge = any_usage g nid;
    is_AbstractMergeNode (kind g merge);

    i = find_index nid (inputs_of (kind g merge));
    phis = (phi_list g merge);
    inps = (phi_inputs g i phis);
    g \<turnstile> inps \<simeq>\<^sub>L inpsE;
    [m, p] \<turnstile> inpsE \<mapsto>\<^sub>L vs;

    m' = set_phis phis vs m\<rbrakk>
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (merge, m', h)" |

  NewInstanceNode:
    "\<lbrakk>kind g nid = (NewInstanceNode nid cname obj nid');
      (h', ref) = h_new_inst h cname; 
      m' = m(nid := ref)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')" |

  LoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode nid f (Some obj) nid');
      g \<turnstile> obj \<simeq> objE; 
      [m, p] \<turnstile> objE \<mapsto> ObjRef ref;
      h_load_field f ref h = v;
      m' = m(nid := v)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h)" |

  SignedDivNode:
    "\<lbrakk>kind g nid = (SignedDivNode nid x y zero sb nxt);
      g \<turnstile> x \<simeq> xe; 
      g \<turnstile> y \<simeq> ye; 
      [m, p] \<turnstile> xe \<mapsto> v1;
      [m, p] \<turnstile> ye \<mapsto> v2;
      v = (intval_div v1 v2);
      m' =  m(nid := v)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  SignedRemNode:
    "\<lbrakk>kind g nid = (SignedRemNode nid x y zero sb nxt);
      g \<turnstile> x \<simeq> xe; 
      g \<turnstile> y \<simeq> ye; 
      [m, p] \<turnstile> xe \<mapsto> v1;
      [m, p] \<turnstile> ye \<mapsto> v2;
      v = (intval_mod v1 v2);
      m' =  m(nid := v)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  StaticLoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode nid f None nid');
      h_load_field f None h = v;
      m' =  m(nid := v)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h)" |

  StoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f newval _ (Some obj) nid');
      g \<turnstile> newval \<simeq> newvalE;
      g \<turnstile> obj \<simeq> objE; 
      [m, p] \<turnstile> newvalE \<mapsto> val;
      [m, p] \<turnstile> objE \<mapsto> ObjRef ref;
      h' = h_store_field f ref val h;
      m' =  m(nid := val)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')" |

  StaticStoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f newval _ None nid');
      g \<turnstile> newval \<simeq> newvalE; 
      [m, p] \<turnstile> newvalE \<mapsto> val;
      h' = h_store_field f None val h;
      m' =  m(nid := val)\<rbrakk> 
    \<Longrightarrow> g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i * i * i \<Rightarrow> o * o * o \<Rightarrow> bool) step .

subsection \<open>Interprocedural Semantics\<close>

type_synonym Signature = "string"
type_synonym Program = "Signature \<rightharpoonup> IRGraph"
type_synonym Classes = "JVMClass list"
type_synonym System = "Program \<times> Classes"

(* 
  Performs a dynamic look-up in the list of instantiated classes to retrieve the appropriate 
  IRGraph to run. Takes: 
    - A System containing the Program and list of classes.
    - The fully-qualified name (dynamic type) of the object which the method has been invoked on.
    - The fully-qualified name of the method invoked. 
*)

function dynamic_lookup :: "System \<Rightarrow> string \<Rightarrow> string \<Rightarrow> IRGraph option" where
  "dynamic_lookup (P,cl) cn mn = (
      if (cl = [] \<or> cn = ''None'')
        then (P mn)
        else (
          if ((find_index (get_simple_signature mn) (simple_signatures cn cl)) = (length (simple_signatures cn cl)))
            then (dynamic_lookup (P, cl) (class_parent (get_JVMClass cn cl)) (get_simple_signature mn))
            else (P (nth (map method_unique_name (get_Methods cn cl))
                   (find_index (get_simple_signature mn) (simple_signatures cn cl))))
        )
      )
  "
  by auto
termination using ownParent by blast 

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
    kind g callTarget = (MethodCallTargetNode targetMethod arguments invoke_kind);
    invoke_kind = Static; 
    S = (P, cl); 
    Some targetGraph = P targetMethod;
    m' = new_map_state;
    g \<turnstile> arguments \<simeq>\<^sub>L argsE;
    [m, p] \<turnstile> argsE  \<mapsto>\<^sub>L p'\<rbrakk>
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#stk, h) \<longrightarrow> ((targetGraph,0,m',p')#(g,nid,m,p)#stk, h)" |

(* TODO Update to use 'hasReceiver' instead of 'invoke_kind \<noteq> Static' *)
  InvokeNodeStep:
  "\<lbrakk>is_Invoke (kind g nid);
    callTarget = ir_callTarget (kind g nid);
    kind g callTarget = (MethodCallTargetNode targetMethod arguments invoke_kind);
    invoke_kind \<noteq> Static; 
    m' = new_map_state;
    g \<turnstile> arguments \<simeq>\<^sub>L argsE;
    [m, p] \<turnstile> argsE  \<mapsto>\<^sub>L p';
    ObjRef self = hd p';
    ObjStr cname = (h_load_field ''class'' self h);
    Some targetGraph = dynamic_lookup S cname (targetMethod)\<rbrakk>
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#stk, h) \<longrightarrow> ((targetGraph,0,m',p')#(g,nid,m,p)#stk, h)" |

(* TODO this produces two parse trees after importing Class *)
  ReturnNode:
  "\<lbrakk>kind g nid = (ReturnNode (Some expr) _);
    g \<turnstile> expr \<simeq> e;
    [m, p] \<turnstile> e \<mapsto> v;

    cm' = cm(cnid := v);
    cnid' = (successors_of (kind cg cnid))!0\<rbrakk> 
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#(cg,cnid,cm,cp)#stk, h) \<longrightarrow> ((cg,cnid',cm',cp)#stk, h)" |

(* TODO this produces two parse trees after importing Class *)
  ReturnNodeVoid:
  "\<lbrakk>kind g nid = (ReturnNode None _);
    cm' = cm(cnid := (ObjRef (Some (2048))));
    
    cnid' = (successors_of (kind cg cnid))!0\<rbrakk> 
    \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#(cg,cnid,cm,cp)#stk, h) \<longrightarrow> ((cg,cnid',cm',cp)#stk, h)" |

  UnwindNode:
  "\<lbrakk>kind g nid = (UnwindNode exception);

    g \<turnstile> exception \<simeq> exceptionE;
    [m, p] \<turnstile> exceptionE \<mapsto> e;
     
    kind cg cnid = (InvokeWithExceptionNode _ _ _ _ _ _ exEdge);

    cm' = cm(cnid := e)\<rbrakk>
  \<Longrightarrow> (S) \<turnstile> ((g,nid,m,p)#(cg,cnid,cm,cp)#stk, h) \<longrightarrow> ((cg,exEdge,cm',cp)#stk, h)"

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
  for P
  where
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
  "graphToSystem graph = ((\<lambda>x. Some graph), [])"

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

