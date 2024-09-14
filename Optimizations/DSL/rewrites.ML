(*  Title:      Optimizations/DSL/rewrites.ML
    Author:     Brae Webb

Generate proof obligation for expression rewrites.
*)

signature RewriteSystem =
sig
val preservation: term;
val termination: term;
val intval: term;
end

signature DSL_REWRITES =
sig
val of_term: binding -> term -> term option -> term -> rewrite;

val preservation_of: Proof.context -> rewrite -> term option -> term;
val termination_of: Proof.context -> rewrite -> term;
val code_of: Proof.context -> rewrite -> term;

val rewrite_cmd: ((binding * Token.src list) * ((string * string) list)) * string -> Proof.context -> Proof.state;

end

functor DSL_Rewrites(System: RewriteSystem): DSL_REWRITES =
struct
fun of_term name term whens source =
  case term of
    (((Const ("Markup.Rewrite.Transform", _)) $ lhs) $ rhs) => 
      {name=name, rewrite=Rule (lhs, rhs, whens), proofs=[], code=[], source=source}
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ lhs) $ rhs) $ cond) => 
      (case whens of 
        NONE =>
        {name=name, rewrite=Rule (lhs, rhs, SOME cond), proofs=[], code=[], source=source} |
        SOME extra =>
        {name=name, rewrite=Rule (lhs, rhs, SOME (@{term "Combine"} $ cond $ extra)), proofs=[], code=[], source=source})
    | _ => raise TERM ("optimization is not a rewrite", [term])


fun result rhs ctxt =
  case type_of (Syntax.check_term (Context.proof_of (Context_Position.set_visible_generic false (Context.Proof ctxt))) rhs) of
    _ => rhs

fun to_term rewrite ctxt = 
  case (#rewrite rewrite) of
    Rule (lhs, rhs, NONE) => 
      (Const ("Markup.Rewrite.Transform", @{typ "IRExpr => IRExpr => (IRExpr, IRExpr) Rewrite"})) $ lhs $ result rhs ctxt
    | Rule (lhs, rhs, SOME cond) => 
      (Const ("Markup.Rewrite.Conditional", @{typ "IRExpr => IRExpr \<Rightarrow> Condition \<Rightarrow> (IRExpr, IRExpr) Rewrite"})) $ lhs $ result rhs ctxt $ cond

fun lhs (term:term) =
  case term of
  (((Const ("Markup.Rewrite.Transform", _)) $ lhs) $ _) => 
      lhs
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ lhs) $ _) $ _) => 
      lhs
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun rhs (term:term) =
  case term of
  (((Const ("Markup.Rewrite.Transform", _)) $ _) $ rhs) => 
      rhs
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ _) $ rhs) $ _) => 
      rhs
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun preservation_of ctxt rewrite assumps =
  case assumps of
    NONE =>
      Syntax.check_prop ctxt 
        (@{const Trueprop} $ (System.preservation $ (to_term rewrite ctxt))) |
    SOME im =>
      Syntax.check_prop ctxt 
        (@{const Pure.imp} $ (@{const Trueprop} $ im) $ (@{const Trueprop} $ (System.preservation $ (to_term rewrite ctxt))))

fun termination_of' ctxt trm rewrite =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.termination $ (to_term rewrite ctxt) $ trm))

fun intval_of ctxt term =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.intval $ term))

fun termination_of ctxt rewrite =
  let
    val state = RewritePhase.current (Proof_Context.theory_of ctxt);
    val trm = (case state of
      NONE => raise TERM ("Optimization phase missing", []) |
      SOME phase => (#trm phase)
    );
  in
    termination_of' ctxt trm rewrite
  end

fun rewrite_lhs (rewrite: rewrite) =
  case (#rewrite rewrite) of
    Rule (lhs, _, _) => lhs

fun rewrite_rhs (rewrite: rewrite) =
  case (#rewrite rewrite) of
    Rule (_, rhs, _) => rhs

fun rewrite_cond (rewrite: rewrite) =
  case (#rewrite rewrite) of
    Rule (_, _, cond) => cond

fun mkstr ctxt name =
  Syntax.read_term ctxt ("STR ''" ^ name ^ "''")

fun create_var ctxt name = 
  (@{term "VariableExprPattern"} $ mkstr ctxt name)

fun create_const ctxt name = 
  (@{term "ConstantVarPattern"} $ mkstr ctxt name)

fun ground_IRExpr ctxt trm =
  (case trm of
    Const ("\<^const>CodeGenAltAlt.PatternExpr.ConstantExprPattern", _) $ (Free (str, _)) => create_const ctxt str
    | Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", _) $ (Free (str, _)) => create_const ctxt str
    | (x $ y) => (ground_IRExpr ctxt x $ ground_IRExpr ctxt y)
    | Abs (str, typ, trm) => Abs (str, typ, ground_IRExpr ctxt trm)
    | Free (str, @{typ PatternExpr}) => create_var ctxt str
    | Free (str, @{typ Value}) => create_const ctxt str
    | _ => trm)

fun ground_Condition_code ctxt trm =
  (case trm of
    (x $ y) => (ground_Condition_code ctxt x $ ground_Condition_code ctxt y)
    | Abs (str, typ, trm) => Abs (str, typ, ground_Condition_code ctxt trm)
    | Free (str, @{typ Condition}) => (@{term "Variable"} $ mkstr ctxt str)
    | _ => trm)

fun type_checked_rewrites ctxt rewrite =
 case (rewrite_cond rewrite) of
    NONE => 
    let
      val [lhs, rhs] =
          (Syntax.check_terms ctxt
            [(rewrite_lhs rewrite),
             (rewrite_rhs rewrite)])
    in
      (lhs, rhs, NONE)
    end
    | SOME c =>
    let
      val c' = ground_Condition_code ctxt (Syntax.check_term ctxt c);
      val [lhs, rhs] =
          (Syntax.check_terms ctxt
            [(rewrite_lhs rewrite),
             (rewrite_rhs rewrite)]);
    in
      (lhs, rhs, SOME c')
    end

fun rewrite_to_term_param ctxt rewrite =
  let 
    val (lhs, rhs, cond) = type_checked_rewrites ctxt rewrite;
  in
    (ground_IRExpr ctxt lhs, ground_IRExpr ctxt rhs,
       case cond of 
        NONE => (Const ("Option.option.None", @{typ "Condition option"})) |
        SOME cond' =>
          (Const ("Option.option.Some", @{typ "Condition => Condition option"}) $ cond'))
  end

fun generate ctxt term =
  let
    val (lhs, rhs, cond) = rewrite_to_term_param ctxt term;
    val generate_term = 
      ((((Const ("CodeGenAltAlt.generateRule", @{typ "PatternExpr \<Rightarrow> Condition option \<Rightarrow> PatternExpr \<Rightarrow> (VarName \<times> Rules)"}))
      $ lhs) $ cond) $ rhs)
    val value = Code_Evaluation.dynamic_value_strict ctxt generate_term;
  in              
    value
  end

fun code_of ctxt rewrite =
  @{const Trueprop} 
  $ ((Const ("HOL.eq", @{typ "(VarName \<times> Rules) \<Rightarrow> (VarName \<times> Rules) \<Rightarrow> bool"})
  $ (Free ((Binding.name_of (#name rewrite)) ^ "_code", @{typ "VarName \<times> Rules"}))
  $ generate ctxt rewrite))


fun add_proofs (rewrite: rewrite) proofs =
  {
    name= #name rewrite,
    rewrite= #rewrite rewrite,
    proofs= proofs,
    code= #code rewrite,
    source= #source rewrite
  }

fun valid_name name =
  not (String.isSubstring "_" name) andalso Char.isUpper (String.sub (name, 0))

fun interpret_when ctxt when =
  let
    val parsed = Syntax.parse_term ctxt when
  in
    parsed
  end

datatype ConditionType = Condition | Prop;

fun select_type when_type =
  case when_type of
    Type ("ConditionDSL.Condition", _) => SOME Condition |
    Type ("HOL.bool", _) => SOME Prop |
    _ => NONE

fun ground_Condition_proof ctxt trm =
  (case trm of
    (x $ y) => (ground_Condition_proof ctxt x $ ground_Condition_proof ctxt y)
    | Abs (str, typ, trm) => Abs (str, typ, ground_Condition_proof ctxt trm)
    | Free (str, @{typ Condition}) => (@{term "Expr"} $ Free (str, @{typ IRExpr}))
    | Free (str, @{typ IRExpr}) => (@{term "Expr"} $ Free (str, @{typ IRExpr}))
    | Free (str, typ) => Free (str, typ)
    | _ => trm)

fun partition ctxt whens =
  let
    val checked = map (Syntax.check_term ctxt) whens;
    val props = (filter (fn when => case (select_type (Term.type_of when)) of SOME Prop => true | _ => false) checked);
    val conds = (filter (fn when => case (select_type (Term.type_of when)) of SOME Condition => true | _ => false) checked);
    val unrek = (filter (fn when => case (select_type (Term.type_of when)) of NONE => true | _ => false) checked);
    val _ = (map (fn when => error ((Pretty.string_of (Syntax.pretty_term ctxt when)) ^ " is not of type bool or Condition")) unrek);
    val _ = (map (fn when => warning ((Pretty.string_of (Syntax.pretty_term ctxt when)) ^ " is a bool condition and therefore not represented in the generated code. This may introduce inconsistencies.")) props);
  in
    (props, conds)
  end

fun generate_condition conditions =
  case conditions of
    [] => NONE |
    [cond] => SOME cond |
    x :: xs => SOME (fold (fn term => fn condition => (@{term "Combine"} $ term $ condition)) xs (x))

fun generate_assumps assumps =
  case assumps of
    [] => NONE |
    [prop] => SOME prop |
    x :: xs => SOME (fold (fn term => fn prop => (@{term "conj"} $ term $ prop)) xs (x))

fun generate_whens ctxt do_ground (whens: ((string * string) list)) =
  let
    val interpretted = (map (interpret_when ctxt o snd) whens);
    val (props, conds) = partition ctxt interpretted;
    val conds = if do_ground then (map (ground_Condition_proof ctxt) conds) else conds;
  in
    (generate_assumps props, generate_condition conds)
  end
val at = @{typ "num \<Rightarrow> 64 word"};
fun rewrite_constants_proofs ctxt is_lhs trm =
  (case trm of
    Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr", typ) $ (Const ("\<^const>Num.numeral_class.numeral", _) $ c)
      => Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr", typ) $ (@{term "IntVal b"} $ (Const ("Num.numeral_class.numeral", at) $ c))
    | Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ (Const ("Num.numeral_class.numeral", _) $ c)
      => Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ (@{term "IntVal b"} $ (Const ("Num.numeral_class.numeral", at) $ c))
    | Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ (Const ("Groups.zero_class.zero", _))
      => Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ (@{term "IntVal b 0"})
    | Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ (Const ("Groups.one_class.one", _))
      => Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ (@{term "IntVal b 0"})
    | Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr", typ) $ e => Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr", typ) $ (if is_lhs then e else IntValMarkup.markup_expr [] ctxt [e])
    | Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ e => Const ("IRTreeEval.IRExpr.ConstantExpr", typ) $ (if is_lhs then e else IntValMarkup.markup_expr [] ctxt [e])
    | (e as (Const ("Markup.Rewrite.Conditional",_))) $ lhs $ rhs $ cond => 
      e $ rewrite_constants_proofs ctxt true lhs $ rewrite_constants_proofs ctxt false rhs $ cond
    | (e as (Const ("Markup.Rewrite.Transform",_))) $ lhs $ rhs => 
      e $ rewrite_constants_proofs ctxt true lhs $ rewrite_constants_proofs ctxt false rhs
    | (x $ y) => (rewrite_constants_proofs ctxt is_lhs x $ rewrite_constants_proofs ctxt is_lhs y)
    | Abs (str, typ, trm) => Abs (str, typ, rewrite_constants_proofs ctxt is_lhs trm)
    | _ => trm)

fun rewrite_constants_code ctxt is_lhs trm =
  (case trm of
    Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (Const ("Num.numeral_class.numeral", _) $ c)
      => Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (@{term "IntVal b"} $ (Const ("Num.numeral_class.numeral", at) $ c))
    | Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (Const ("Groups.zero_class.zero", _))
      => Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (@{term "IntVal b 0"})
    | Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (Const ("Groups.one_class.one", _))
      => Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (@{term "IntVal b 0"})
    | Const ("\<^const>CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (Free (str, _)) => create_const ctxt str
    | Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ (Free (str, _)) => create_const ctxt str
    | Const ("\<^const>CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ e => 
      (if is_lhs then trm else
       (Const ("\<^const>CodeGenAltAlt.PatternExpr.ConstantLiteralPattern", @{typ "PatternExpr \<Rightarrow> PatternExpr"})
        $ (ground_IRExpr ctxt (Syntax.check_term ctxt (PatternExprMarkup.markup_expr [] ctxt [e])))))
    | Const ("CodeGenAltAlt.PatternExpr.ConstantExprPattern", typ) $ e => 
      (if is_lhs then trm else
       (Const ("CodeGenAltAlt.PatternExpr.ConstantLiteralPattern", @{typ "PatternExpr \<Rightarrow> PatternExpr"})
         $ (ground_IRExpr ctxt (Syntax.check_term ctxt (PatternExprMarkup.markup_expr [] ctxt [e])))))
    | (e as (Const ("Markup.Rewrite.Conditional",_))) $ lhs $ rhs $ cond => 
      e $ rewrite_constants_code ctxt true lhs $ rewrite_constants_code ctxt false rhs $ cond
    | (e as (Const ("Markup.Rewrite.Transform",_))) $ lhs $ rhs => 
      e $ rewrite_constants_code ctxt true lhs $ rewrite_constants_code ctxt false rhs
    | (x $ y) => (rewrite_constants_code ctxt is_lhs x $ rewrite_constants_code ctxt is_lhs y)
    | Abs (str, typ, trm) => Abs (str, typ, rewrite_constants_code ctxt is_lhs trm)
    | _ => trm)

fun rewrite_cmd (((bind: binding, options), whens), opt) ctxt = 
  let
    val name = Binding.name_of bind;
    val _ = (if valid_name name then () 
             else (warning "Optimization name should be UpperCase not snake_case or camelCase"));
    
    val intval = case options of [[token]] => Token.content_of token = "intval" | _ => false;    
    val notactic = case options of [[token]] => Token.content_of token = "notactic" | _ => false;
    val nogen = case options of [[token]] => Token.content_of token = "nogen" | _ => false;
    
    val raw_term = (Syntax.parse_term ctxt opt);
    val (assumps, conditions) = generate_whens ctxt true whens;
    (*val _ = @{print} (Syntax.pretty_term ctxt conditions);*)

    (*val rewrite = of_term bind raw_term conditions raw_term;
    val raw_term = to_term rewrite ctxt;*)

    val term = IRExprMarkup.markup_expr [] ctxt [(Type.strip_constraints raw_term)];
    val term = rewrite_constants_proofs ctxt false term;
    val rewrite = of_term bind term conditions raw_term;

    val intval_preservation = (if intval 
      then intval_of ctxt (IntValMarkup.markup_expr [term] ctxt [(Syntax.parse_term ctxt opt)])
      else @{term True})
    val extra = (if intval then [(intval_preservation, [intval_preservation])] else [])
                                  
    val preservation = preservation_of ctxt rewrite assumps;
    val preservation = if intval 
      then @{term "Pure.imp"} $ intval_preservation $ preservation
      else preservation;
    val termination = termination_of ctxt rewrite;

    val code = if nogen then @{term True} else (let
      val (_, code_conditions) = generate_whens ctxt false whens;
      val pattern_term = PatternExprMarkup.markup_expr [] ctxt [(Type.strip_constraints raw_term)];
      val pattern_term = rewrite_constants_code ctxt false pattern_term;
      val pattern_rewrite = of_term bind pattern_term code_conditions raw_term;
      in 
        code_of ctxt pattern_rewrite
      end)

    val register = fn proofs => RewritePhase.register (bind, (add_proofs rewrite proofs));

    fun after_qed thms lthy =
      let
        val lthy' = Local_Theory.background_theory (register (hd thms)) lthy;

        val lthy'' = snd (if nogen then ((@{term True}, ("", @{thm All_def})), lthy') else
        (Specification.definition
            NONE [] []
            ((Binding.suffix_name "_code" bind, []), code)
            lthy'
        ))
      in
        snd (Local_Theory.note ((bind, []), hd thms) lthy'')
      end

    val target = (Proof.theorem NONE after_qed 
        [extra @ [(preservation, [preservation]), (termination, [termination])]] ctxt);

    val apply = (Proof.apply 
      ((Method.Source (Token.make_src ("unfold_optimization", Position.start) [])),
        Position.no_range) target);

    val result = if notactic then target else (case Seq.hd apply of
       Seq.Result r => r
       | Seq.Error _ => target);

    val apply = (Proof.apply
      ((Method.Source (Token.make_src ("unfold_size", Position.start) [])),
       Position.no_range) (Proof.defer 1 result));

    val result = if notactic then target else (case Seq.hd apply of
       Seq.Result r => r
       | Seq.Error _ => result);
  in
    result
  end

end