theory Class
  imports Main
begin

text \<open> Representation of a standard class containing fields, methods and constructors \<close>

text \<open> ----- Representation of Fields and Parameters ----- \<close>

type_synonym FieldName = "string"
type_synonym FieldType = "string"
type_synonym ParameterType = "string"

datatype JVMField = 
  NewField (field_name: FieldName)
           (field_type: FieldType) |
  NewParameter (parameter_type: ParameterType)

text \<open> ----- Representation of a Method ----- \<close>

type_synonym MethodName = "string"
type_synonym ReturnType = "string"
type_synonym MethodParameters = "JVMField list"
type_synonym MethodUniqueName = "string"

(* TODO could extend this to include exceptions throwable? *)
datatype JVMMethod = 
  NewMethod (method_name: MethodName)
            (method_returnType: ReturnType)
            (method_parameters: MethodParameters)
            (method_unique_name: MethodUniqueName)

text \<open> ----- Representation of a Constructor ----- \<close>

type_synonym ConstructorParameters = "JVMField list"

datatype JVMConstructor = 
  NewConstructor (constructor_params: ConstructorParameters)

text \<open> ----- Representation of a standard class ----- \<close>

type_synonym Fields = "JVMField list"
type_synonym Methods = "JVMMethod list"
type_synonym Constructors = "JVMConstructor list"

type_synonym ClassName = "string"
type_synonym ParentClass = "string"

datatype JVMClass = 
  NewClass (class_name: ClassName) 
           (class_fields: Fields) 
           (class_methods: Methods) 
           (class_constructors: Constructors)  
           (class_parents: "ParentClass list")
           (class_parent: ParentClass)

(* Empty placeholder class *)
definition emptyClass :: "JVMClass" where 
  "emptyClass = NewClass ''name_empty'' [] [] [] [] ''parent_empty''"

(* java.lang.Object *)
definition jlObject :: "JVMClass" where
  "jlObject = NewClass 
     ''java.lang.Object''
		[]
		[NewMethod ''finalize'' ''V'' [] ''java.lang.Object.finalize()V'', 
     NewMethod ''wait'' ''V'' [NewParameter ''J'', NewParameter ''I''] ''java.lang.Object.wait(JI)V'', 
     NewMethod ''wait'' ''V'' [] ''java.lang.Object.wait()V'', 
     NewMethod ''wait'' ''V'' [NewParameter ''J''] ''java.lang.Object.wait(J)V'', 
     NewMethod ''equals'' ''Z'' [NewParameter ''java.lang.Object''] ''java.lang.Object.equals(java.lang.Object)Z'', 
     NewMethod ''toString'' ''java.lang.String'' [] ''java.lang.Object.toString()java.lang.String'', 
     NewMethod ''hashCode'' ''I'' [] ''java.lang.Object.hashCode()I'', 
     NewMethod ''getClass'' ''java.lang.Class'' [] ''java.lang.Object.getClass()java.lang.Class'', 
     NewMethod ''clone'' ''java.lang.Object'' [] ''java.lang.Object.clone()java.lang.Object'', 
     NewMethod ''notify'' ''V'' [] ''java.lang.Object.notify()V'', 
     NewMethod ''notifyAll'' ''V'' [] ''java.lang.Object.notifyAll()V'']
		[NewConstructor []] 
    [''None'']
		''None''"

text \<open> ----- General Functions ----- \<close>

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

text \<open> ----- Functions to interact with JVMClass lists ----- \<close>

(* Returns the index of a class in the JVMClass list *)
fun find_class_index :: "string \<Rightarrow> JVMClass list \<Rightarrow> nat" where
  "find_class_index name cl = find_index name (map class_name cl)"

(* Returns a JVMClass given its name and the JVMClass mapping *)
fun get_JVMClass :: "string \<Rightarrow> JVMClass list \<Rightarrow> JVMClass" where 
  "get_JVMClass cName cList = 
    (if ((find_class_index cName cList) = (length cList)) 
      then (emptyClass) 
      else (nth cList (find_class_index cName cList)))" 

(* Returns the methods belonging to a particular class, given its name and the JVMClass mapping *)
fun get_Methods :: "string \<Rightarrow> JVMClass list \<Rightarrow> JVMMethod list" where
  "get_Methods cname clist = class_methods (get_JVMClass cname clist)"

(* Returns the simple signature of a method (e.g., "plus(I)I") given its fully-qualified name *)
fun get_simple_signature :: "string \<Rightarrow> string" where
  "get_simple_signature fqn = rev (take (find_index (CHR ''.'') (rev fqn)) (rev fqn))"

(* Returns the simple signatures of all the methods belonging to a given class *)
fun simple_signatures :: "string \<Rightarrow> JVMClass list \<Rightarrow> string list" where
  "simple_signatures cname clist = 
    (map get_simple_signature (map method_unique_name (get_Methods cname clist)))"

fun classNames :: "JVMClass list \<Rightarrow> string set" where
  "classNames cl = set (map class_name cl)"

fun parentRel :: "JVMClass list \<Rightarrow> string rel" where
  "parentRel cl = (set (map (\<lambda>c. (class_name c, class_parent c)) cl))"

fun parentRel2 :: "JVMClass list \<Rightarrow> (string \<times> string) list" where
  "parentRel2 cl = (map (\<lambda>c. (class_name c, class_parent c)) cl)"

fun parentOf :: "JVMClass list \<Rightarrow> (string \<rightharpoonup> string)" where
  "parentOf [] = Map.empty" |
  "parentOf (c#cl) = (parentOf cl)((class_name c) \<mapsto> (class_parent c))"

fun superclassOf :: "JVMClass list \<Rightarrow> (string rel)" where
  "superclassOf cl = trancl (parentRel cl)"

lemma "finite (set (l::('a list)))" 
  by simp

lemma domainUnion: 
  "dom (m(a\<mapsto>b)) = dom (m) \<union> {a}" 
  by simp

lemma "finite (dom (parentOf m))"  
  proof (induction m)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a m)
  then show ?case unfolding parentOf.simps
    by (metis insert_def singleton_conv sup_commute finite.simps domainUnion) 
qed

lemma wellFoundedParent:
  assumes "acyclic (parentRel cl)"
  shows "wf (parentRel cl)" 
  using assms unfolding parentRel.simps by (metis (no_types, lifting) wf_set)

lemma transSuperClassOf[simp]:
  "trans (superclassOf cl)"
  by simp

(** ----- Testing ----- **)

(*

public class bestClassEver extends Object {

    private int x;
    private float y;

    public bestClassEver(int x) {
        this.x = x;
    }
    
    public bestClassEver(float y) {
        this.y = y;
    }
    
    public int getX() {
        return this.x;
    }
    
    public void setY(float newY) {
        this.y = newY;
    }
}

*)

definition bestClassEver :: "JVMClass" where 
  "bestClassEver = 
    NewClass ''bestClassEver'' 
             [NewField ''x'' ''I'', NewField ''y'' ''float''] 
             [NewMethod ''getX'' ''I'' [NewParameter ''null''] ''bestClassEver_getXI(n)'', 
              NewMethod ''setY'' ''null'' [NewParameter ''float''] ''bestClassEver_SetYn(f)''] 
             [NewConstructor [NewParameter ''I''], NewConstructor [NewParameter ''float'']] 
             [''Object'']
             ''Object''"

(* Testing class-based functions *)
value "class_name bestClassEver"
value "class_parent bestClassEver"
value "class_fields bestClassEver"
value "class_methods bestClassEver"
value "class_constructors bestClassEver"

(* Testing field-based functions *)
value "field_name (hd (class_fields bestClassEver))"
value "field_type (hd (class_fields bestClassEver))"

value "field_name (hd (tl (class_fields bestClassEver)))"
value "field_type (hd (tl (class_fields bestClassEver)))"

(* Testing method-based functions *)
value "method_name (hd (class_methods bestClassEver))"
value "method_returnType (hd (class_methods bestClassEver))"
value "method_parameters (hd (class_methods bestClassEver))"
value "method_unique_name (hd (class_methods bestClassEver))"

value "method_name (hd (tl (class_methods bestClassEver)))"
value "method_returnType (hd (tl (class_methods bestClassEver)))"
value "method_parameters (hd (tl (class_methods bestClassEver)))"
value "method_unique_name (hd (tl (class_methods bestClassEver)))"

(* Testing constructor-based functions *)
value "constructor_params (hd (class_constructors bestClassEver))"

value "constructor_params (hd (tl (class_constructors bestClassEver)))"

(* Testing parameter-based functions *)
value "parameter_type (hd (method_parameters (hd (class_methods bestClassEver))))"
value "parameter_type (hd (method_parameters (hd (tl (class_methods bestClassEver)))))"

value "parameter_type (hd (constructor_params (hd (class_constructors bestClassEver))))"
value "parameter_type (hd (constructor_params (hd (tl (class_constructors bestClassEver)))))"


(* Samples from Java translator *)
definition unit_InstanceOfTest_instanceOfSnippet4_mapping :: "JVMClass list" where
	"unit_InstanceOfTest_instanceOfSnippet4_mapping = [
	NewClass ''org.graalvm.compiler.core.test.InstanceOfTest$B''
		[]
		[]
		[NewConstructor []]
		[''org.graalvm.compiler.core.test.InstanceOfTest$A'', ''java.lang.Object'', ''None'']
		''org.graalvm.compiler.core.test.InstanceOfTest$A'',

	NewClass ''org.graalvm.compiler.core.test.InstanceOfTest$A''
		[]
		[]
		[NewConstructor []]
		[''java.lang.Object'', ''None'']
		''java.lang.Object'',

	NewClass ''java.lang.Object''
		[]
		[NewMethod ''finalize'' ''V'' [] ''java.lang.Object.finalize()V'', NewMethod ''wait'' ''V'' [NewParameter ''J'', NewParameter ''I''] ''java.lang.Object.wait(JI)V'', NewMethod ''wait'' ''V'' [] ''java.lang.Object.wait()V'', NewMethod ''wait'' ''V'' [NewParameter ''J''] ''java.lang.Object.wait(J)V'', NewMethod ''equals'' ''Z'' [NewParameter ''java.lang.Object''] ''java.lang.Object.equals(java.lang.Object)Z'', NewMethod ''toString'' ''java.lang.String'' [] ''java.lang.Object.toString()java.lang.String'', NewMethod ''hashCode'' ''I'' [] ''java.lang.Object.hashCode()I'', NewMethod ''getClass'' ''java.lang.Class'' [] ''java.lang.Object.getClass()java.lang.Class'', NewMethod ''clone'' ''java.lang.Object'' [] ''java.lang.Object.clone()java.lang.Object'', NewMethod ''notify'' ''V'' [] ''java.lang.Object.notify()V'', NewMethod ''notifyAll'' ''V'' [] ''java.lang.Object.notifyAll()V'']
		[NewConstructor []]
		[''None'']
		''None'']"

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

(* Testing out functions *)
value "parentRel unit_InvokeVirtual_01_test_mapping"
value "superclassOf unit_InvokeVirtual_01_test_mapping"
value "classNames unit_InvokeVirtual_01_test_mapping"
value "the (parentOf unit_InvokeVirtual_01_test_mapping ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'')"
value "set (simple_signatures ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' unit_InvokeVirtual_01_test_mapping)"

value "find_class_index ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' unit_InvokeVirtual_01_test_mapping"
value "get_JVMClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B'' unit_InvokeVirtual_01_test_mapping"
value "get_simple_signature ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I''"

(* Lemmas to help with Classes invariants *)
definition inheritsFromObject :: "JVMClass list \<Rightarrow> bool" where
  "inheritsFromObject cl = ((remdups (map List.last (map class_parents cl))) = [''None''])"

lemma containsObjImplies[simp]: 
  shows "List.member cl jlObject \<longrightarrow> 
        (''java.lang.Object'',''None'') \<in> parentRel cl \<longrightarrow> 
        List.member (parentRel2 cl) (''java.lang.Object'',''None'')" 
  using List.member_def by fastforce

lemma containsObjImpliesNonEmpty:
  shows "List.member cl jlObject \<longrightarrow> cl \<noteq> []"
  using List.member_def by force

lemma acyclic_jlObj:
  shows "acyclic (parentRel [jlObject])" 
  by (simp add: jlObject_def wf_acyclic)

lemma inheritsFromObj_jlObj:
  shows "inheritsFromObject [jlObject]"
  unfolding inheritsFromObject_def jlObject_def by simp 
    
lemma acyclicDef: 
  fixes cl :: "JVMClass list"
  shows "acyclic (parentRel cl) \<Longrightarrow> (\<forall>j. j \<in> (set cl) \<longrightarrow> (class_name j \<noteq> class_parent j))"
  unfolding acyclic_def by auto

lemma acyclicParent_super:
  shows "(acyclic (parentRel cl)) \<Longrightarrow> (acyclic (superclassOf cl))"
  unfolding parentRel.simps superclassOf.simps acyclic_def by simp

lemma remdupsInherit:
  shows "inheritsFromObject cl \<Longrightarrow> inheritsFromObject (remdups cl)"
  using inheritsFromObject_def by (simp add: remdups_map_remdups)

typedef Classes = "{cl :: JVMClass list . 
                    List.member cl jlObject \<and>
                    cl \<noteq> [] \<and> 
                    acyclic (parentRel cl) \<and>
                    inheritsFromObject cl \<and>
                    distinct cl}" 
  morphisms classToJVMList Abs_Classes
proof -
  obtain cl where cl: "cl = [jlObject]" 
    by simp
  then have a: "cl \<noteq> []" 
    by simp
  have b: "List.member cl jlObject"
    by (simp add: member_rec(1) cl)
  have c: "acyclic (parentRel cl)"
    using acyclic_jlObj by (simp add: cl)
  have d: "inheritsFromObject cl"
    by (simp add: cl inheritsFromObj_jlObj)
  have e: "distinct cl"
    by (simp add: cl)
  then show ?thesis 
    using cl b c d by blast 
qed

(* Equality *)
lemma classes_eq_iff:
  "cl1 = cl2 \<longleftrightarrow> classToJVMList cl1 = classToJVMList cl2" 
  by (simp add: classToJVMList_inject)

lemma classes_eqI:
  "classToJVMList cl1 = classToJVMList cl2 \<Longrightarrow> cl1 = cl2" 
  by (simp add: classToJVMList_inject)

(* Constructor *)
setup_lifting type_definition_Classes

lift_definition JVMClasses :: "JVMClass list \<Rightarrow> Classes" is
  "\<lambda>j. (if (List.member j jlObject \<and> acyclic (parentRel j) \<and> inheritsFromObject j) 
        then (if (distinct j) then j else (remdups j))
        else [jlObject])"
  using List.member_def acyclic_jlObj containsObjImpliesNonEmpty inheritsFromObj_jlObj 
        remdupsInherit 
  by fastforce

(* Maintaining invariant *)
lemma nonempty_cl [simp, intro]:
  "(classToJVMList cl) \<noteq> []" 
  using classToJVMList [of cl] by simp

lemma containsjlobj_cl [simp, intro]:
  "List.member (classToJVMList cl) jlObject"
  using classToJVMList [of cl] by simp

lemma acyclic_cl [simp, intro]:
  "acyclic (parentRel (classToJVMList cl))"
  using classToJVMList [of cl] by simp

lemma inheritsFromObj_cl [simp, intro]:
  "inheritsFromObject (classToJVMList cl)"
  using classToJVMList [of cl] by simp

lemma distinct_cl [simp, intro]:
  "distinct (classToJVMList cl)"
  using classToJVMList [of cl] by simp

lemma original_jvm [simp]:
  "classToJVMList (JVMClasses cl) = 
      (if (List.member cl jlObject \<and> acyclic (parentRel cl) \<and> inheritsFromObject cl) 
       then (if (distinct cl) then cl else (remdups cl)) 
       else [jlObject])"
  using JVMClasses.rep_eq by auto

(* Abstraction transformation *)
lemma classesToClasses [simp, code abstype]:
  "JVMClasses (classToJVMList cl) = cl" 
  using acyclic_cl classes_eqI by auto  

(* Operations *)
context
begin

(* empty = contains java.lang.Object only *)
qualified definition empty :: "Classes" where
  "empty = JVMClasses []"

qualified definition mapJVMFunc :: "(JVMClass \<Rightarrow> 'b) \<Rightarrow> Classes \<Rightarrow> 'b list" where
  "mapJVMFunc cf cl = List.map cf (classToJVMList cl)"

qualified definition member :: "Classes \<Rightarrow> JVMClass \<Rightarrow> bool" where
  "member cl c = List.member (classToJVMList cl) c"

qualified definition length :: "Classes \<Rightarrow> nat" where
  "length cl = List.length (classToJVMList cl)"

qualified definition nth :: "Classes \<Rightarrow> nat \<Rightarrow> JVMClass" where
  "nth cl n = List.nth (classToJVMList cl) n"

end

(* Code gen version with invariant maintained *)
lemma classToJVM_empty [simp, code abstract]:
  "classToJVMList Class.empty = [jlObject]"
  by (metis JVMClasses.rep_eq containsObjImpliesNonEmpty Class.empty_def)

lemma classToJVM_map [simp, code]:
  "(Class.mapJVMFunc f cl) = List.map f (classToJVMList cl)"
  by (simp add: Class.mapJVMFunc_def)

(* Code gen setup *)
code_datatype JVMClasses

lemma [code]:
  "classToJVMList (JVMClasses cl) = 
      (if (List.member cl jlObject \<and> acyclic (parentRel cl) \<and> inheritsFromObject cl) 
      then (if (distinct cl) then cl else (remdups cl)) 
      else [jlObject])" 
  by (simp add: JVMClasses.rep_eq)

(* Testing code gen *)
definition newclass :: "Classes" where
  "newclass = JVMClasses [NewClass ''name'' [] [] [] [''parent'', ''None''] ''parent'', jlObject, jlObject]"

definition cyclicClass :: "JVMClass list" where
  "cyclicClass = [NewClass ''name'' [] [] [] [''name''] ''name'']"

value "newclass"
value "classToJVMList newclass" 
value "Class.mapJVMFunc class_name newclass"
value "Class.mapJVMFunc class_parent newclass"

(* invalid; java.lang.Object*)
value "classToJVMList (JVMClasses [])"
value "classToJVMList (JVMClasses cyclicClass)" 
value "acyclic (parentRel cyclicClass)"                               (* False *)
value "acyclic (parentRel (classToJVMList (JVMClasses cyclicClass)))" (* True *)

(* Redefining some functions in terms of Classes, not JVMClass list *)
(* TODO update original functions to these *)

(* Returns the index of a class in the Classes list *)
fun CLfind_class_index :: "string \<Rightarrow> Classes \<Rightarrow> nat" where
  "CLfind_class_index name cl = find_index name (Class.mapJVMFunc class_name cl)"

(* Returns a JVMClass given its name and the Classes list *)
fun CLget_JVMClass :: "string \<Rightarrow> Classes \<Rightarrow> JVMClass" where 
  "CLget_JVMClass cName cList = 
    (if ((CLfind_class_index cName cList) = (Class.length cList)) 
      then (emptyClass) 
      else (Class.nth cList (CLfind_class_index cName cList)))" 

(* Returns the methods belonging to a particular class, given its name and the Classes list *)
fun CLget_Methods :: "string \<Rightarrow> Classes \<Rightarrow> JVMMethod list" where
  "CLget_Methods cname clist = class_methods (CLget_JVMClass cname clist)"

(* Returns the simple signatures of all the methods belonging to a given class *)
fun CLsimple_signatures :: "string \<Rightarrow> Classes \<Rightarrow> string list" where
  "CLsimple_signatures cname clist = 
      (map get_simple_signature (map method_unique_name (CLget_Methods cname clist)))"

lemma finiteSuper: 
  fixes cl :: "Classes"
  shows "finite (superclassOf (classToJVMList cl))" 
  by simp

lemma finiteClasses:
  fixes cl :: "Classes"
  shows "finite (set (classToJVMList cl))" 
  by simp

end
