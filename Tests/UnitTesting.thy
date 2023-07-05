section \<open>Testing of IR Semantics based on GraalVM Unit Tests\<close>

theory UnitTesting
  imports
    Semantics.IRStepObj
begin

declare [[ML_source_trace]]

subsection \<open>Unit test helper functions\<close>

inductive static_test :: "IRGraph \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>config0 = (g, 0, new_map_state, ps);
    (\<lambda>x. None, JVMClasses []) \<turnstile> ([config0, config0], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l \<rbrakk>
    \<Longrightarrow> static_test g ps ((prod.fst(prod.snd(prod.snd end))) 0)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testE) static_test .


(* get the return value of the top-most function *)
fun get_result :: "(IRGraph \<times> ID \<times> MapState \<times> Params) \<Rightarrow> Value" where
  "get_result (g,i,m,p) = m 0"

(* Defines case where a unit test returns void *)
definition VOID_RETURN :: "Value" where
  "VOID_RETURN = (ObjRef (Some (2048)))"


text \<open>$object_test$ and $program_test$ run a static initialisation block first
   (to initialise static fields etc.), then a named method graph.  
  The $program_test$ driver takes an expected result value as an input,
  whereas the $object_test$ driver takes a result-checking function as input.
  This result-checking function is given the output heap as well as the result of the method,
  so that it can check various fields or properties of the method output.
  \<close>
inductive object_test :: "System \<Rightarrow> Signature \<Rightarrow> Value list \<Rightarrow> (Value \<Rightarrow> FieldRefHeap \<Rightarrow> bool) => bool"
  where
  InitStatics:
  "\<lbrakk>S = (prog, cl);
    Some init = prog '''';
    config0 = (init, 0, new_map_state, ps);
    (prog,cl) \<turnstile> ([config0, config0], new_heap) | [] \<longrightarrow>* ((end1 # xs1), heap1) | l1;
    
    Some g = prog m;
    config1 = (g, 0, new_map_state, ps);
    (prog,cl) \<turnstile> ([config1, config1], heap1) | [] \<longrightarrow>* ((end2 # xs2), heap2) | l2;
    result = get_result end2;
    checker result heap2 \<rbrakk>
    \<Longrightarrow> object_test S m ps checker" |

  NoStatics:
  "\<lbrakk>S = (prog, cl);
    '''' \<notin> dom prog;
    Some g = prog m;
    config1 = (g, 0, new_map_state, ps);
    (prog,cl) \<turnstile> ([config1, config1], new_heap) | [] \<longrightarrow>* ((end2 # xs2), heap2) | l2;
    result = get_result end2;
    checker result heap2 \<rbrakk>
    \<Longrightarrow> object_test S m ps checker"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testObj) object_test .

inductive program_test :: "System \<Rightarrow> Signature \<Rightarrow> Value list \<Rightarrow> Value => bool"
  where
  "object_test S m ps (\<lambda> x h. x = result)
    \<Longrightarrow> program_test S m ps result"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testP) program_test .

text \<open>$exception_test$ handles tests where an exception is thrown as opposed to
      there being a return result to compare to. The $exception_test$ checks that
      the expected exception type occurs at the expected node ID in the graph.\<close>

datatype ExitCause =
  NormalReturn |
  Exception ID string

fun getException :: "nat list \<Rightarrow> IRGraph \<Rightarrow> nat" where
  "getException (x#xs) g = (if (is_BytecodeExceptionNode(kind g x)) then x else (getException xs g))"

inductive exception_test :: "System
      \<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> Value list) list \<times> FieldRefHeap
      \<Rightarrow> ExitCause
      \<Rightarrow> bool"
  for p where
  "\<lbrakk>kind g nid = (UnwindNode exception);
    is_BytecodeExceptionNode (kind g exception);
    type = stp_type (stamp g exception)\<rbrakk>
    \<Longrightarrow> exception_test p (((g,nid,m,ps)#stk),h) (Exception exception type)" |

  (* Currently only supports ValuePhiNode *)
  "\<lbrakk>kind g nid = (UnwindNode exception);
    \<not>(is_BytecodeExceptionNode (kind g exception));

    is_ValuePhiNode (kind g exception);
    inps = ir_values (kind g exception);
    inps \<noteq> [];
    exceptionNode = getException inps g;

    ObjRef reference = m exception;
    ObjStr type = h_load_field ''class'' reference h \<rbrakk>
    \<Longrightarrow> exception_test p (((g,nid,m,ps)#stk),h) (Exception exceptionNode type)" |

  "\<lbrakk>p \<turnstile> (((g,nid,m,ps)#stk),h) \<longrightarrow> (((g',nid',m',ps')#stk'),h');
    exception_test p (((g',nid',m',ps')#stk'),h') es\<rbrakk>
    \<Longrightarrow> exception_test p (((g,nid,m,ps)#stk),h) es" |

  "\<lbrakk>p \<turnstile> (((g,nid,m,ps)#stk),h) \<longrightarrow> (((g',nid',m',ps')#stk'),h');
    has_return m'\<rbrakk>
    \<Longrightarrow> exception_test p (((g,nid,m,ps)#stk),h) NormalReturn"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as assertTest,
                  i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as assertTestOut)
          "exception_test" .

subsection \<open>Unit test helper functions - Debug versions\<close>

inductive program_test_debug :: "System \<Rightarrow> Signature \<Rightarrow> Value list \<Rightarrow> nat \<Rightarrow> ID \<times> MapState \<times> Params \<Rightarrow> bool"
  where
  NoStatics:
  "\<lbrakk>S = (prog, cl);
    '''' \<notin> dom prog;
    Some g = prog m;
    config1 = (g, 0, new_map_state, ps);
    exec_debug S ([config1, config1], new_heap) steps ((end2 # xs2), heap2)\<rbrakk>
    \<Longrightarrow> program_test_debug S m ps steps (prod.snd end2)"
(* output end2 has type: "(IRGraph \<times> ID \<times> MapState \<times> Params)" *)
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testPin,
                  i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as testPout) program_test_debug .

(* Example of using program_test_debug:
values "{m | m . program_test_debug prog mathodName paramList steps m}"
*)

inductive static_test_debug :: "IRGraph \<Rightarrow> Value list \<Rightarrow> nat \<Rightarrow>  ID \<times> MapState \<times> Params \<Rightarrow> bool"
  where
  "program_test_debug ((Map.empty (''_'' \<mapsto> g)), JVMClasses []) ''_'' ps steps out 
   \<Longrightarrow> static_test_debug g ps steps out"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testGin,
                  i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as testGout) static_test_debug .

(* Example of using static_test_debug:
values "{m | m . static_test_debug graph paramList steps m}"
*)



subsection \<open>Start of Translated Unit Tests\<close>




(* temporary back-compatible functions for tests *)
fun IntVal32 :: "int64 \<Rightarrow> Value" where
  "IntVal32 val = new_int 32 val"

fun IntVal64 :: "int64 \<Rightarrow> Value" where
  "IntVal64 val = new_int 64 val"

(* Lorg/graalvm/compiler/jtt/micro/InvokeVirtual_01_Interface;.InvokeVirtual_01_Interface_test*)
definition unit_InvokeVirtual_01_Interface_test :: Program where
  "unit_InvokeVirtual_01_Interface_test = Map.empty (
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerEqualsNode 1 4), VoidStamp),
  (6, (BeginNode 18), VoidStamp),
  (7, (BeginNode 9), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::aObject'' None 11), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (10, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.count1()I'' [9] Virtual), VoidStamp),
  (11, (InvokeNode 11 10 None None (Some 12) 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (FrameState [] None None None), IllegalStamp),
  (13, (ReturnNode (Some 11) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (IntegerEqualsNode 1 14), VoidStamp),
  (16, (BeginNode 29), VoidStamp),
  (17, (BeginNode 19), VoidStamp),
  (18, (IfNode 15 17 16), VoidStamp),
  (19, (LoadFieldNode 19 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::aObject'' None 22), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (IsNullNode 19), VoidStamp),
  (22, (FixedGuardNode 21 None 25), VoidStamp),
  (23, (PiNode 19 (Some 22)), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False True False),
  (24, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (25, (ReturnNode (Some 24) None), VoidStamp),
  (26, (IntegerEqualsNode 1 24), VoidStamp),
  (27, (BeginNode 41), VoidStamp),
  (28, (BeginNode 30), VoidStamp),
  (29, (IfNode 26 28 27), VoidStamp),
  (30, (LoadFieldNode 30 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::aObject'' None 32), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (31, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.returnsSomething()Z'' [30] Virtual), VoidStamp),
  (32, (InvokeNode 32 31 None None (Some 33) 36), IntegerStamp 32 (0) (1)),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (IntegerEqualsNode 32 4), VoidStamp),
  (36, (ReturnNode (Some 32) None), VoidStamp),
  (37, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (38, (IntegerEqualsNode 1 37), VoidStamp),
  (39, (BeginNode 50), VoidStamp),
  (40, (BeginNode 42), VoidStamp),
  (41, (IfNode 38 40 39), VoidStamp),
  (42, (LoadFieldNode 42 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::bObject'' None 44), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (43, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.count1()I'' [42] Virtual), VoidStamp),
  (44, (InvokeNode 44 43 None None (Some 45) 46), IntegerStamp 32 (-2147483648) (2147483647)),
  (45, (FrameState [] None None None), IllegalStamp),
  (46, (ReturnNode (Some 44) None), VoidStamp),
  (47, (IntegerEqualsNode 1 3), VoidStamp),
  (48, (BeginNode 60), VoidStamp),
  (49, (BeginNode 51), VoidStamp),
  (50, (IfNode 47 49 48), VoidStamp),
  (51, (LoadFieldNode 51 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::cObject'' None 53), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (52, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.count1()I'' [51] Virtual), VoidStamp),
  (53, (InvokeNode 53 52 None None (Some 54) 55), IntegerStamp 32 (-2147483648) (2147483647)),
  (54, (FrameState [] None None None), IllegalStamp),
  (55, (ReturnNode (Some 53) None), VoidStamp),
  (56, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (57, (IntegerEqualsNode 1 56), VoidStamp),
  (58, (BeginNode 73), VoidStamp),
  (59, (BeginNode 63), VoidStamp),
  (60, (IfNode 57 59 58), VoidStamp),
  (61, (ConstantNode (new_int 32 (30))), IntegerStamp 32 (30) (30)),
  (62, (ConstantNode (new_int 32 (34))), IntegerStamp 32 (34) (34)),
  (63, (LoadFieldNode 63 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::bObject'' None 66), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (64, (FrameState [] None None None), IllegalStamp),
  (65, (IsNullNode 63), VoidStamp),
  (66, (FixedGuardNode 65 None 68), VoidStamp),
  (67, (PiNode 63 (Some 66)), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False True False),
  (68, (ReturnNode (Some 4) None), VoidStamp),
  (69, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (70, (IntegerEqualsNode 1 69), VoidStamp),
  (71, (BeginNode 89), VoidStamp),
  (72, (BeginNode 76), VoidStamp),
  (73, (IfNode 70 72 71), VoidStamp),
  (74, (ConstantNode (new_int 32 (17))), IntegerStamp 32 (17) (17)),
  (75, (ConstantNode (new_int 32 (21))), IntegerStamp 32 (21) (21)),
  (76, (LoadFieldNode 76 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::cObject'' None 79), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (77, (FrameState [] None None None), IllegalStamp),
  (78, (IsNullNode 76), VoidStamp),
  (79, (FixedGuardNode 78 None 84), VoidStamp),
  (80, (PiNode 76 (Some 79)), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False True False),
  (81, (ConstantNode (new_int 32 (42))), IntegerStamp 32 (42) (42)),
  (82, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (83, (ConstantNode (new_int 32 (52))), IntegerStamp 32 (52) (52)),
  (84, (ReturnNode (Some 83) None), VoidStamp),
  (85, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (86, (IntegerEqualsNode 1 85), VoidStamp),
  (87, (BeginNode 101), VoidStamp),
  (88, (BeginNode 90), VoidStamp),
  (89, (IfNode 86 88 87), VoidStamp),
  (90, (LoadFieldNode 90 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::bObject'' None 92), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (91, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.returnsSomething()Z'' [90] Virtual), VoidStamp),
  (92, (InvokeNode 92 91 None None (Some 93) 96), IntegerStamp 32 (0) (1)),
  (93, (FrameState [] None None None), IllegalStamp),
  (94, (IntegerEqualsNode 92 4), VoidStamp),
  (96, (ReturnNode (Some 92) None), VoidStamp),
  (97, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (98, (IntegerEqualsNode 1 97), VoidStamp),
  (99, (BeginNode 109), VoidStamp),
  (100, (BeginNode 102), VoidStamp),
  (101, (IfNode 98 100 99), VoidStamp),
  (102, (LoadFieldNode 102 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::cObject'' None 104), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' False False False),
  (103, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.returnsSomething()Z'' [102] Virtual), VoidStamp),
  (104, (InvokeNode 104 103 None None (Some 105) 108), IntegerStamp 32 (0) (1)),
  (105, (FrameState [] None None None), IllegalStamp),
  (106, (IntegerEqualsNode 104 4), VoidStamp),
  (108, (ReturnNode (Some 104) None), VoidStamp),
  (109, (ReturnNode (Some 81) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::aObject'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (NewInstanceNode 6 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$B'' None 10), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$B'' True True False),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] (Some 8) None None), IllegalStamp),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::bObject'' 6 (Some 11) None 12), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (NewInstanceNode 12 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$C'' None 16), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$C'' True True False),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (FrameState [] (Some 14) None None), IllegalStamp),
  (16, (StoreFieldNode 16 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface::cObject'' 12 (Some 17) None 18), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.count1()I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.returnsSomething()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$C.returnsSomething()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$B.count1()I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]
  )"

definition unit_InvokeVirtual_01_Interface_test_mapping :: "JVMClass list" where
	"unit_InvokeVirtual_01_Interface_test_mapping = [
	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$C''
		[]
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$C.plus(I)I'', NewMethod ''returnsSomething'' ''Z'' [] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$C.returnsSomething()Z'']
		[NewConstructor []]
		[''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'', ''java.lang.Object'', ''None'']
		''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'',

	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$B''
		[]
		[NewMethod ''count1'' ''I'' [] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$B.count1()I'', NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$B.plus(I)I'']
		[NewConstructor []]
		[''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'', ''java.lang.Object'', ''None'']
		''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A'',

	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A''
		[]
		[NewMethod ''count1'' ''I'' [] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.count1()I'', NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.plus(I)I'', NewMethod ''fl1'' ''I'' [] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.fl1()I'', NewMethod ''returnsSomething'' ''Z'' [] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface$A.returnsSomething()Z'']
		[NewConstructor []]
		[''java.lang.Object'', ''None'']
		''java.lang.Object'',

	NewClass ''java.lang.Object''
		[]
		[NewMethod ''finalize'' ''V'' [] ''java.lang.Object.finalize()V'', NewMethod ''wait'' ''V'' [NewParameter ''J'', NewParameter ''I''] ''java.lang.Object.wait(JI)V'', NewMethod ''wait'' ''V'' [] ''java.lang.Object.wait()V'', NewMethod ''wait'' ''V'' [NewParameter ''J''] ''java.lang.Object.wait(J)V'', NewMethod ''equals'' ''Z'' [NewParameter ''java.lang.Object''] ''java.lang.Object.equals(java.lang.Object)Z'', NewMethod ''toString'' ''java.lang.String'' [] ''java.lang.Object.toString()java.lang.String'', NewMethod ''hashCode'' ''I'' [] ''java.lang.Object.hashCode()I'', NewMethod ''getClass'' ''java.lang.Class'' [] ''java.lang.Object.getClass()java.lang.Class'', NewMethod ''clone'' ''java.lang.Object'' [] ''java.lang.Object.clone()java.lang.Object'', NewMethod ''notify'' ''V'' [] ''java.lang.Object.notify()V'', NewMethod ''notifyAll'' ''V'' [] ''java.lang.Object.notifyAll()V'']
		[NewConstructor []]
		[''None'']
		''None'']"

value "program_test (unit_InvokeVirtual_01_Interface_test, JVMClasses unit_InvokeVirtual_01_Interface_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.test(I)I'' [(new_int 32 (0))] (new_int 32 (1))"

value "program_test (unit_InvokeVirtual_01_Interface_test, JVMClasses unit_InvokeVirtual_01_Interface_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.test(I)I'' [(new_int 32 (1))] (new_int 32 (2))"

value "program_test (unit_InvokeVirtual_01_Interface_test, JVMClasses unit_InvokeVirtual_01_Interface_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.test(I)I'' [(new_int 32 (4))] (new_int 32 (1))"

value "program_test (unit_InvokeVirtual_01_Interface_test, JVMClasses unit_InvokeVirtual_01_Interface_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.test(I)I'' [(new_int 32 (5))] (new_int 32 (0))"

value "program_test (unit_InvokeVirtual_01_Interface_test, JVMClasses unit_InvokeVirtual_01_Interface_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.test(I)I'' [(new_int 32 (7))] (new_int 32 (1))"

value "program_test (unit_InvokeVirtual_01_Interface_test, JVMClasses unit_InvokeVirtual_01_Interface_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01_Interface.test(I)I'' [(new_int 32 (8))] (new_int 32 (0))"

(* Lorg/graalvm/compiler/jtt/micro/InvokeVirtual_01;.InvokeVirtual_01_test*)
definition unit_InvokeVirtual_01_test :: Program where
  "unit_InvokeVirtual_01_test = Map.empty (
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 17), VoidStamp),
  (6, (BeginNode 8), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (LoadFieldNode 8 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::aObject'' None 10), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' False False False),
  (9, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' [8, 1] Virtual), VoidStamp),
  (10, (InvokeNode 10 9 None None (Some 11) 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (ReturnNode (Some 10) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (IntegerEqualsNode 1 13), VoidStamp),
  (15, (BeginNode 27), VoidStamp),
  (16, (BeginNode 18), VoidStamp),
  (17, (IfNode 14 16 15), VoidStamp),
  (18, (LoadFieldNode 18 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::bObject'' None 20), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' False False False),
  (19, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' [18, 1] Virtual), VoidStamp),
  (20, (InvokeNode 20 19 None None (Some 21) 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 20) None), VoidStamp),
  (23, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (24, (IntegerEqualsNode 1 23), VoidStamp),
  (25, (BeginNode 34), VoidStamp),
  (26, (BeginNode 28), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (LoadFieldNode 28 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::cObject'' None 30), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' False False False),
  (29, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' [28, 1] Virtual), VoidStamp),
  (30, (InvokeNode 30 29 None None (Some 31) 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (FrameState [] None None None), IllegalStamp),
  (32, (ReturnNode (Some 30) None), VoidStamp),
  (33, (ConstantNode (new_int 32 (42))), IntegerStamp 32 (42) (42)),
  (34, (ReturnNode (Some 33) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::aObject'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (NewInstanceNode 6 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B'' None 10), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B'' True True False),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] (Some 8) None None), IllegalStamp),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::bObject'' 6 (Some 11) None 12), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (NewInstanceNode 12 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C'' None 16), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C'' True True False),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (FrameState [] (Some 14) None None), IllegalStamp),
  (16, (StoreFieldNode 16 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::cObject'' 12 (Some 17) None 18), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ReturnNode (Some 2) None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C.plus(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (20))), IntegerStamp 32 (20) (20)),
  (5, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B.plus(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (5, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]
  )"

definition unit_InvokeVirtual_01_test_mapping :: "JVMClass list" where
	"unit_InvokeVirtual_01_test_mapping = [
	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B''
		[]
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B.plus(I)I'']
		[NewConstructor []]
		[''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'', ''java.lang.Object'', ''None'']
		''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'',

	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C''
		[]
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C.plus(I)I'']
		[NewConstructor []]
		[''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'', ''java.lang.Object'', ''None'']
		''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'',

	NewClass ''java.lang.Object''
		[]
		[NewMethod ''finalize'' ''V'' [] ''java.lang.Object.finalize()V'', NewMethod ''wait'' ''V'' [NewParameter ''J'', NewParameter ''I''] ''java.lang.Object.wait(JI)V'', NewMethod ''wait'' ''V'' [] ''java.lang.Object.wait()V'', NewMethod ''wait'' ''V'' [NewParameter ''J''] ''java.lang.Object.wait(J)V'', NewMethod ''equals'' ''Z'' [NewParameter ''java.lang.Object''] ''java.lang.Object.equals(java.lang.Object)Z'', NewMethod ''toString'' ''java.lang.String'' [] ''java.lang.Object.toString()java.lang.String'', NewMethod ''hashCode'' ''I'' [] ''java.lang.Object.hashCode()I'', NewMethod ''getClass'' ''java.lang.Class'' [] ''java.lang.Object.getClass()java.lang.Class'', NewMethod ''clone'' ''java.lang.Object'' [] ''java.lang.Object.clone()java.lang.Object'', NewMethod ''notify'' ''V'' [] ''java.lang.Object.notify()V'', NewMethod ''notifyAll'' ''V'' [] ''java.lang.Object.notifyAll()V'']
		[NewConstructor []]
		[''None'']
		''None'',

	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A''
		[]
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'']
		[NewConstructor []]
		[''java.lang.Object'', ''None'']
		''java.lang.Object'']"

value "program_test (unit_InvokeVirtual_01_test, JVMClasses unit_InvokeVirtual_01_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (0))] (new_int 32 (0))"

value "program_test (unit_InvokeVirtual_01_test, JVMClasses unit_InvokeVirtual_01_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (1))] (new_int 32 (11))"

value "program_test (unit_InvokeVirtual_01_test, JVMClasses unit_InvokeVirtual_01_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (2))] (new_int 32 (22))"

value "program_test (unit_InvokeVirtual_01_test, JVMClasses unit_InvokeVirtual_01_test_mapping) ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (3))] (new_int 32 (42))"

(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_b;.BC_getstatic_b_test*)
definition unit_BC_getstatic_b_test :: Program where
  "unit_BC_getstatic_b_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.test()B'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b::field'' None 3), IntegerStamp 32 (-128) (127)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (ConstantNode (new_int 8 (11))), IntegerStamp 8 (11) (11)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test (unit_BC_getstatic_b_test, JVMClasses []) ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.test()B'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_c;.BC_getstatic_c_test*)
definition unit_BC_getstatic_c_test :: Program where
  "unit_BC_getstatic_c_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.test()C'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c::field'' None 3), IntegerStamp 32 (0) (65535)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (ConstantNode (new_int 16 (11))), IntegerStamp 16 (11) (11)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test (unit_BC_getstatic_c_test, JVMClasses []) ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.test()C'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_i;.BC_getstatic_i_test*)
definition unit_BC_getstatic_i_test :: Program where
  "unit_BC_getstatic_i_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.test()I'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i::field'' None 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i::field'' 2 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test (unit_BC_getstatic_i_test, JVMClasses []) ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.test()I'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_l;.BC_getstatic_l_test*)
definition unit_BC_getstatic_l_test :: Program where
  "unit_BC_getstatic_l_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.test()J'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l::field'' None 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (11))), IntegerStamp 64 (11) (11)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l::field'' 2 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test (unit_BC_getstatic_l_test, JVMClasses []) ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.test()J'' [] (IntVal 64 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_s;.BC_getstatic_s_test*)
definition unit_BC_getstatic_s_test :: Program where
  "unit_BC_getstatic_s_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.test()S'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s::field'' None 3), IntegerStamp 32 (-32768) (32767)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (ConstantNode (new_int 16 (11))), IntegerStamp 16 (11) (11)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test (unit_BC_getstatic_s_test, JVMClasses []) ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.test()S'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_z;.BC_getstatic_z_test*)
definition unit_BC_getstatic_z_test :: Program where
  "unit_BC_getstatic_z_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.test()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z::field'' None 3), IntegerStamp 32 (0) (1)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.<clinit>()V'' [] Static), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test (unit_BC_getstatic_z_test, JVMClasses []) ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.test()Z'' [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2b;.BC_i2b_testInt*)
definition unit_BC_i2b_testInt_100 :: IRGraph where  "unit_BC_i2b_testInt_100 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2b_testInt_100  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_testInt_100  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_i2b_testInt_100  [(new_int 32 (255))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_testInt_100  [(new_int 32 (128))] (new_int 32 (-128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2b;.BC_i2b_testLong*)
definition unit_BC_i2b_testLong_104 :: IRGraph where  "unit_BC_i2b_testLong_104 = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (SignExtendNode 8 64 3), IntegerStamp 64 (-128) (127)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_BC_i2b_testLong_104  [(new_int 32 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_i2b_testLong_104  [(new_int 32 (2))] (IntVal 64 (2))"

value "static_test unit_BC_i2b_testLong_104  [(new_int 32 (255))] (IntVal 64 (-1))"

value "static_test unit_BC_i2b_testLong_104  [(new_int 32 (128))] (IntVal 64 (-128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2b;.BC_i2b_test*)
definition unit_BC_i2b_test_96 :: IRGraph where  "unit_BC_i2b_test_96 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2b_test_96  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_test_96  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_i2b_test_96  [(new_int 32 (255))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_test_96  [(new_int 32 (128))] (new_int 32 (-128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2c;.BC_i2c_testInt*)
definition unit_BC_i2c_testInt_111 :: IRGraph where  "unit_BC_i2c_testInt_111 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2c_testInt_111  [(new_int 32 (-1))] (new_int 32 (65535))"

value "static_test unit_BC_i2c_testInt_111  [(new_int 32 (645))] (new_int 32 (645))"

value "static_test unit_BC_i2c_testInt_111  [(new_int 32 (65535))] (new_int 32 (65535))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2c;.BC_i2c_testLong*)
definition unit_BC_i2c_testLong_114 :: IRGraph where  "unit_BC_i2c_testLong_114 = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ZeroExtendNode 16 64 3), IntegerStamp 64 (0) (65535)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_BC_i2c_testLong_114  [(new_int 32 (-1))] (IntVal 64 (65535))"

value "static_test unit_BC_i2c_testLong_114  [(new_int 32 (645))] (IntVal 64 (645))"

value "static_test unit_BC_i2c_testLong_114  [(new_int 32 (65535))] (IntVal 64 (65535))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2c;.BC_i2c_test*)
definition unit_BC_i2c_test_108 :: IRGraph where  "unit_BC_i2c_test_108 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2c_test_108  [(new_int 32 (-1))] (new_int 32 (65535))"

value "static_test unit_BC_i2c_test_108  [(new_int 32 (645))] (new_int 32 (645))"

value "static_test unit_BC_i2c_test_108  [(new_int 32 (65535))] (new_int 32 (65535))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2l;.BC_i2l_test*)
definition unit_BC_i2l_test_127 :: IRGraph where  "unit_BC_i2l_test_127 = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (SignExtendNode 32 64 1), IntegerStamp 64 (-2147483648) (2147483647)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BC_i2l_test_127  [(new_int 32 (1))] (IntVal 64 (1))"

value "static_test unit_BC_i2l_test_127  [(new_int 32 (2))] (IntVal 64 (2))"

value "static_test unit_BC_i2l_test_127  [(new_int 32 (3))] (IntVal 64 (3))"

value "static_test unit_BC_i2l_test_127  [(new_int 32 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_i2l_test_127  [(new_int 32 (-2147483647))] (IntVal 64 (-2147483647))"

value "static_test unit_BC_i2l_test_127  [(new_int 32 (-2147483648))] (IntVal 64 (-2147483648))"

value "static_test unit_BC_i2l_test_127  [(new_int 32 (2147483647))] (IntVal 64 (2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2s;.BC_i2s_testInt*)
definition unit_BC_i2s_testInt_138 :: IRGraph where  "unit_BC_i2s_testInt_138 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2s_testInt_138  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_testInt_138  [(new_int 32 (34))] (new_int 32 (34))"

value "static_test unit_BC_i2s_testInt_138  [(new_int 32 (65535))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_testInt_138  [(new_int 32 (32768))] (new_int 32 (-32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2s;.BC_i2s_testLong*)
definition unit_BC_i2s_testLong_142 :: IRGraph where  "unit_BC_i2s_testLong_142 = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (SignExtendNode 16 64 3), IntegerStamp 64 (-32768) (32767)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_BC_i2s_testLong_142  [(new_int 32 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_i2s_testLong_142  [(new_int 32 (34))] (IntVal 64 (34))"

value "static_test unit_BC_i2s_testLong_142  [(new_int 32 (65535))] (IntVal 64 (-1))"

value "static_test unit_BC_i2s_testLong_142  [(new_int 32 (32768))] (IntVal 64 (-32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2s;.BC_i2s_test*)
definition unit_BC_i2s_test_134 :: IRGraph where  "unit_BC_i2s_test_134 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2s_test_134  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_test_134  [(new_int 32 (34))] (new_int 32 (34))"

value "static_test unit_BC_i2s_test_134  [(new_int 32 (65535))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_test_134  [(new_int 32 (32768))] (new_int 32 (-32768))"



(* Lorg/graalvm/compiler/jtt/bytecode/BC_iadd2;.BC_iadd2_test*)
definition unit_BC_iadd2_test_153 :: IRGraph where  "unit_BC_iadd2_test_153 = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iadd2_test_153  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iadd2_test_153  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iadd2_test_153  [(new_int 32 (33)), (new_int 32 (67))] (new_int 32 (100))"

value "static_test unit_BC_iadd2_test_153  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iadd2_test_153  [(new_int 32 (-128)), (new_int 32 (1))] (new_int 32 (-127))"

value "static_test unit_BC_iadd2_test_153  [(new_int 32 (127)), (new_int 32 (1))] (new_int 32 (128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iadd3;.BC_iadd3_test*)
definition unit_BC_iadd3_test_159 :: IRGraph where  "unit_BC_iadd3_test_159 = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iadd3_test_159  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iadd3_test_159  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iadd3_test_159  [(new_int 32 (33)), (new_int 32 (67))] (new_int 32 (100))"

value "static_test unit_BC_iadd3_test_159  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iadd3_test_159  [(new_int 32 (-128)), (new_int 32 (1))] (new_int 32 (-127))"

value "static_test unit_BC_iadd3_test_159  [(new_int 32 (127)), (new_int 32 (1))] (new_int 32 (128))"

value "static_test unit_BC_iadd3_test_159  [(new_int 32 (-32768)), (new_int 32 (1))] (new_int 32 (-32767))"

value "static_test unit_BC_iadd3_test_159  [(new_int 32 (32767)), (new_int 32 (1))] (new_int 32 (32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iadd;.BC_iadd_test*)
definition unit_BC_iadd_test_146 :: IRGraph where  "unit_BC_iadd_test_146 = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iadd_test_146  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iadd_test_146  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iadd_test_146  [(new_int 32 (33)), (new_int 32 (67))] (new_int 32 (100))"

value "static_test unit_BC_iadd_test_146  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iadd_test_146  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483647))"

value "static_test unit_BC_iadd_test_146  [(new_int 32 (2147483647)), (new_int 32 (1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_iadd_test_146  [(new_int 32 (-2147483647)), (new_int 32 (-2))] (new_int 32 (2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iand;.BC_iand_test*)
definition unit_BC_iand_test_187 :: IRGraph where  "unit_BC_iand_test_187 = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AndNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iand_test_187  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_BC_iand_test_187  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iand_test_187  [(new_int 32 (31)), (new_int 32 (63))] (new_int 32 (31))"

value "static_test unit_BC_iand_test_187  [(new_int 32 (6)), (new_int 32 (4))] (new_int 32 (4))"

value "static_test unit_BC_iand_test_187  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iconst;.BC_iconst_test*)
definition unit_BC_iconst_test_196 :: IRGraph where  "unit_BC_iconst_test_196 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 8), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ReturnNode (Some 3) None), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerEqualsNode 1 9), VoidStamp),
  (11, (BeginNode 19), VoidStamp),
  (12, (BeginNode 14), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ReturnNode (Some 9) None), VoidStamp),
  (15, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (16, (IntegerEqualsNode 1 15), VoidStamp),
  (17, (BeginNode 25), VoidStamp),
  (18, (BeginNode 20), VoidStamp),
  (19, (IfNode 16 18 17), VoidStamp),
  (20, (ReturnNode (Some 15) None), VoidStamp),
  (21, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (22, (IntegerEqualsNode 1 21), VoidStamp),
  (23, (BeginNode 31), VoidStamp),
  (24, (BeginNode 26), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (ReturnNode (Some 21) None), VoidStamp),
  (27, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (28, (IntegerEqualsNode 1 27), VoidStamp),
  (29, (BeginNode 37), VoidStamp),
  (30, (BeginNode 32), VoidStamp),
  (31, (IfNode 28 30 29), VoidStamp),
  (32, (ReturnNode (Some 27) None), VoidStamp),
  (33, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (34, (IntegerEqualsNode 1 33), VoidStamp),
  (35, (BeginNode 40), VoidStamp),
  (36, (BeginNode 38), VoidStamp),
  (37, (IfNode 34 36 35), VoidStamp),
  (38, (ReturnNode (Some 33) None), VoidStamp),
  (39, (ConstantNode (new_int 32 (375))), IntegerStamp 32 (375) (375)),
  (40, (ReturnNode (Some 39) None), VoidStamp)
  ]"
value "static_test unit_BC_iconst_test_196  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iconst_test_196  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_iconst_test_196  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iconst_test_196  [(new_int 32 (3))] (new_int 32 (3))"

value "static_test unit_BC_iconst_test_196  [(new_int 32 (4))] (new_int 32 (4))"

value "static_test unit_BC_iconst_test_196  [(new_int 32 (5))] (new_int 32 (5))"

value "static_test unit_BC_iconst_test_196  [(new_int 32 (6))] (new_int 32 (375))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv2;.BC_idiv2_test*)
definition unit_BC_idiv2_test_208 :: IRGraph where  "unit_BC_idiv2_test_208 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv2_test_208  [(new_int 32 (-2147483648)), (new_int 32 (-1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_idiv2_test_208  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483648))"


(* Lorg/graalvm/compiler/jtt/except/BC_idiv2;.BC_idiv2_test*)
definition unit_BC_idiv2_test_771 :: IRGraph where  "unit_BC_idiv2_test_771 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv2_test_771  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_idiv_16;.BC_idiv_16_test*)
definition unit_BC_idiv_16_test_800 :: IRGraph where  "unit_BC_idiv_16_test_800 = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerEqualsNode 1 4), VoidStamp),
  (6, (BeginNode 18), VoidStamp),
  (7, (BeginNode 17), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (10, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (11, (RightShiftNode 2 10), IntegerStamp 32 (-1) (0)),
  (12, (ConstantNode (new_int 32 (28))), IntegerStamp 32 (28) (28)),
  (13, (UnsignedRightShiftNode 11 12), IntegerStamp 32 (0) (15)),
  (14, (AddNode 13 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (16, (RightShiftNode 14 15), IntegerStamp 32 (-134217728) (134217727)),
  (17, (ReturnNode (Some 16) None), VoidStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (0)), (new_int 32 (16))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (0)), (new_int 32 (17))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (0)), (new_int 32 (-16))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (0)), (new_int 32 (-17))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (0)), (new_int 32 (-1024))] (new_int 32 (-64))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (1)), (new_int 32 (16))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (1)), (new_int 32 (17))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (1)), (new_int 32 (-16))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (1)), (new_int 32 (-17))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test_800  [(new_int 32 (1)), (new_int 32 (-1024))] (new_int 32 (-64))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_idiv_4;.BC_idiv_4_test*)
definition unit_BC_idiv_4_test_814 :: IRGraph where  "unit_BC_idiv_4_test_814 = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (4, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (5, (RightShiftNode 1 4), IntegerStamp 32 (-1) (0)),
  (6, (ConstantNode (new_int 32 (30))), IntegerStamp 32 (30) (30)),
  (7, (UnsignedRightShiftNode 5 6), IntegerStamp 32 (0) (3)),
  (8, (AddNode 7 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (RightShiftNode 8 9), IntegerStamp 32 (-536870912) (536870911)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_4_test_814  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_idiv_4_test_814  [(new_int 32 (4))] (new_int 32 (1))"

value "static_test unit_BC_idiv_4_test_814  [(new_int 32 (5))] (new_int 32 (1))"

value "static_test unit_BC_idiv_4_test_814  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_idiv_4_test_814  [(new_int 32 (-4))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_4_test_814  [(new_int 32 (-5))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_4_test_814  [(new_int 32 (-256))] (new_int 32 (-64))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv_overflow;.BC_idiv_overflow_test*)
definition unit_BC_idiv_overflow_test_210 :: IRGraph where  "unit_BC_idiv_overflow_test_210 = irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (OrNode 2 4), IntegerStamp 32 (-2147483647) (2147483647)),
  (6, (SignedDivNode 6 1 5 None None 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_overflow_test_210  [(new_int 32 (-2147483648)), (new_int 32 (-1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_idiv_overflow_test_210  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483648))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv;.BC_idiv_testStrictlyPositive*)
definition unit_BC_idiv_testStrictlyPositive_207 :: IRGraph where  "unit_BC_idiv_testStrictlyPositive_207 = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (64))), IntegerStamp 32 (64) (64)),
  (4, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (5, (AndNode 1 4), IntegerStamp 32 (0) (7)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (AddNode 5 6), IntegerStamp 32 (1) (8)),
  (8, (SignedDivNode 8 3 7 None None 9), IntegerStamp 32 (8) (64)),
  (9, (ReturnNode (Some 8) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_testStrictlyPositive_207  [(new_int 32 (6))] (new_int 32 (9))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv;.BC_idiv_test*)
definition unit_BC_idiv_test_203 :: IRGraph where  "unit_BC_idiv_test_203 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_test_203  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_BC_idiv_test_203  [(new_int 32 (2)), (new_int 32 (-1))] (new_int 32 (-2))"

value "static_test unit_BC_idiv_test_203  [(new_int 32 (256)), (new_int 32 (4))] (new_int 32 (64))"

value "static_test unit_BC_idiv_test_203  [(new_int 32 (135)), (new_int 32 (7))] (new_int 32 (19))"


(* Lorg/graalvm/compiler/jtt/except/BC_idiv;.BC_idiv_test*)
definition unit_BC_idiv_test_770 :: IRGraph where  "unit_BC_idiv_test_770 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_test_770  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq_2;.BC_ifeq_2_test*)
definition unit_BC_ifeq_2_test_220 :: IRGraph where  "unit_BC_ifeq_2_test_220 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (ConditionalNode 4 5 3), IntegerStamp 32 (0) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_2_test_220  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BC_ifeq_2_test_220  [(new_int 32 (1))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq_3;.BC_ifeq_3_test*)
definition unit_BC_ifeq_3_test_222 :: IRGraph where  "unit_BC_ifeq_3_test_222 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (ConditionalNode 4 3 5), IntegerStamp 32 (0) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_3_test_222  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ifeq_3_test_222  [(new_int 32 (1))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_testCondb*)
definition unit_BC_ifeq_testCondb_217 :: IRGraph where  "unit_BC_ifeq_testCondb_217 = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (ConstantNode (new_int 32 (255))), IntegerStamp 32 (255) (255)),
  (6, (ZeroExtendNode 8 32 3), IntegerStamp 32 (0) (255)),
  (7, (IntegerEqualsNode 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (ConditionalNode 7 8 9), IntegerStamp 32 (0) (1)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_testCondb_217  [(new_int 32 (255))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_testCondc*)
definition unit_BC_ifeq_testCondc_219 :: IRGraph where  "unit_BC_ifeq_testCondc_219 = irgraph [
  (0, (StartNode (Some 2) 10), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (6, (IntegerEqualsNode 4 5), VoidStamp),
  (7, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (8, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (9, (ConditionalNode 6 7 8), IntegerStamp 32 (0) (1)),
  (10, (ReturnNode (Some 9) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_testCondc_219  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_testConds*)
definition unit_BC_ifeq_testConds_218 :: IRGraph where  "unit_BC_ifeq_testConds_218 = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (6, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (7, (IntegerEqualsNode 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (ConditionalNode 7 8 9), IntegerStamp 32 (0) (1)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_testConds_218  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_test*)
definition unit_BC_ifeq_test_212 :: IRGraph where  "unit_BC_ifeq_test_212 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (BeginNode 24), VoidStamp),
  (18, (IfNode 4 17 16), VoidStamp),
  (19, (AddNode 14 10), IntegerStamp 32 (-2) (0)),
  (21, (AddNode 14 8), IntegerStamp 32 (0) (2)),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode [22, 24] (Some 26) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (ValuePhiNode 25 [19, 21] 23), IntegerStamp 32 (-2) (2)),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (ReturnNode (Some 25) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_test_212  [(new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_BC_ifeq_test_212  [(new_int 32 (1))] (new_int 32 (-2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifge_2;.BC_ifge_2_test*)
definition unit_BC_ifge_2_test_227 :: IRGraph where  "unit_BC_ifge_2_test_227 = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ConditionalNode 4 5 6), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BC_ifge_2_test_227  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_BC_ifge_2_test_227  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BC_ifge_2_test_227  [(new_int 32 (1)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_ifge_2_test_227  [(new_int 32 (0)), (new_int 32 (-100))] (new_int 32 (1))"

value "static_test unit_BC_ifge_2_test_227  [(new_int 32 (-1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ifge_2_test_227  [(new_int 32 (-12)), (new_int 32 (-12))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifge_3;.BC_ifge_3_test*)
definition unit_BC_ifge_3_test_233 :: IRGraph where  "unit_BC_ifge_3_test_233 = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (ConditionalNode 4 5 6), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BC_ifge_3_test_233  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_ifge_3_test_233  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ifge_3_test_233  [(new_int 32 (1)), (new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_BC_ifge_3_test_233  [(new_int 32 (0)), (new_int 32 (-100))] (new_int 32 (0))"

value "static_test unit_BC_ifge_3_test_233  [(new_int 32 (-1)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BC_ifge_3_test_233  [(new_int 32 (-12)), (new_int 32 (-12))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifge;.BC_ifge_test*)
definition unit_BC_ifge_test_224 :: IRGraph where  "unit_BC_ifge_test_224 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 24), VoidStamp),
  (17, (BeginNode 22), VoidStamp),
  (18, (IfNode 4 17 16), VoidStamp),
  (19, (AddNode 14 10), IntegerStamp 32 (-2) (0)),
  (21, (AddNode 14 8), IntegerStamp 32 (0) (2)),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode [22, 24] (Some 26) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (ValuePhiNode 25 [19, 21] 23), IntegerStamp 32 (-2) (2)),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (ReturnNode (Some 25) None), VoidStamp)
  ]"
value "static_test unit_BC_ifge_test_224  [(new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_BC_ifge_test_224  [(new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_BC_ifge_test_224  [(new_int 32 (-1))] (new_int 32 (-2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifgt;.BC_ifgt_test*)
definition unit_BC_ifgt_test_239 :: IRGraph where  "unit_BC_ifgt_test_239 = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (BeginNode 13), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [4, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 24), VoidStamp),
  (17, (BeginNode 22), VoidStamp),
  (18, (IfNode 5 17 16), VoidStamp),
  (19, (AddNode 14 10), IntegerStamp 32 (-2) (0)),
  (21, (AddNode 14 4), IntegerStamp 32 (0) (2)),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode [22, 24] (Some 26) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (ValuePhiNode 25 [19, 21] 23), IntegerStamp 32 (-2) (2)),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (ReturnNode (Some 25) None), VoidStamp)
  ]"
value "static_test unit_BC_ifgt_test_239  [(new_int 32 (0))] (new_int 32 (-2))"

value "static_test unit_BC_ifgt_test_239  [(new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_BC_ifgt_test_239  [(new_int 32 (-1))] (new_int 32 (-2))"

end