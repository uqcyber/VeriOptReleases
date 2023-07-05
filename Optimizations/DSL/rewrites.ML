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
val of_term: binding -> term -> term -> rewrite;

val preservation_of: Proof.context -> rewrite -> term;
val termination_of: Proof.context -> rewrite -> term;
val code_of: Proof.context -> rewrite -> term;

val rewrite_cmd: (binding * Token.src list) * string -> Proof.context -> Proof.state;

end

functor DSL_Rewrites(System: RewriteSystem): DSL_REWRITES =
struct
fun of_term name term source =
  case term of
    (((Const ("Markup.Rewrite.Transform", _)) $ lhs) $ rhs) => 
      {name=name, rewrite=Transform (lhs, rhs), proofs=[], code=[], source=source}
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ lhs) $ rhs) $ cond) => 
      {name=name, rewrite=Conditional (lhs, rhs, cond), proofs=[], code=[], source=source}
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun to_term rewrite = 
  case (#rewrite rewrite) of
    Transform (lhs, rhs) => 
      (Const ("Markup.Rewrite.Transform", @{typ "IRExpr => IRExpr => IRExpr Rewrite"})) $ lhs $ rhs
    | Conditional (lhs, rhs, cond) => 
      (Const ("Markup.Rewrite.Conditional", @{typ "IRExpr => IRExpr \<Rightarrow> SideCondition \<Rightarrow> IRExpr Rewrite"})) $ lhs $ rhs $ cond
    | _ => raise TERM ("rewrite cannot be translated yet", [])

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

fun preservation_of ctxt rewrite =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.preservation $ (to_term rewrite)))

fun termination_of' ctxt trm rewrite =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.termination $ (to_term rewrite) $ trm))

fun intval_of ctxt term =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.intval $ term))

fun value_def ctxt name rewrite =
  ((Const ("Pure.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> prop"})
  $ (Free ("val_" ^ (Binding.name_of name), @{typ "bool"}))
  $ (
      (((Const ("HOL.eq", @{typ "Value \<Rightarrow> Value \<Rightarrow> bool"}))
      $ (IntValMarkup.markup_expr [] ctxt [lhs rewrite])
      $ (IntValMarkup.markup_expr [] ctxt [rhs rewrite])))
    )))

fun val_def_const ctxt name rewrite =
  @{const Trueprop}
  $ ((Const ("HOL.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
  $ (Free ("val_" ^ (Binding.name_of name), @{typ "bool"}))
  $ (
      ((Const ("HOL.eq", @{typ "int \<Rightarrow> int \<Rightarrow> bool"}))
      (*$ Var (("x", 0), @{typ int})*)
      $ @{term "(10::int) + (-(12::int))"}
      $ @{term "(10::int) + (-(12::int))"}))
    ))

fun word_def ctxt name rewrite =
  ((Const ("HOL.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
  $ (Free ("word_" ^ name, @{typ "bool"}))
  $ (
      (@{const Trueprop}
      $ ((Const ("HOL.eq", @{typ "('a::len) word \<Rightarrow> 'a word \<Rightarrow> bool"}))
      $ (WordMarkup.markup_expr [] ctxt [lhs rewrite])
      $ (WordMarkup.markup_expr [] ctxt [rhs rewrite])))
    )))

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
    Transform (lhs, _) => lhs
    | Conditional (lhs, _, _) => lhs
    | _ => raise TERM ("rewrite cannot be translated yet", [])

fun rewrite_rhs (rewrite: rewrite) =
  case (#rewrite rewrite) of
    Transform (_, rhs) => rhs
    | Conditional (_, rhs, _) => rhs
    | _ => raise TERM ("rewrite cannot be translated yet", [])

fun rewrite_cond (rewrite: rewrite) =
  case (#rewrite rewrite) of
    Transform (_, _) => @{term "Empty"}
    | Conditional (_, _, cond) => cond
    | _ => raise TERM ("rewrite cannot be translated yet", [])

fun mkstr ctxt name =
  Syntax.read_term ctxt ("STR ''" ^ name ^ "''")

fun create_var ctxt name = 
  @{term "VariableExpr"} $ mkstr ctxt name $ @{term "VoidStamp"}

fun create_const ctxt name = 
  (@{term "ConstantVar"} $ mkstr ctxt name)

fun ground_IRExpr ctxt trm =
  (case trm of
    Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr", _) $ (Free (str, _)) => create_const ctxt str
    | Const ("IRTreeEval.IRExpr.ConstantExpr", _) $ (Free (str, _)) => create_const ctxt str
    | (x $ y) => (ground_IRExpr ctxt x $ ground_IRExpr ctxt y)
    | Abs (str, typ, trm) => Abs (str, typ, ground_IRExpr ctxt trm)
    | Free (str, @{typ IRExpr}) => create_var ctxt str
    | Free (str, @{typ Value}) => create_const ctxt str
    | _ => trm)

fun type_checked_rewrites ctxt rewrite =
  let
    val [lhs, rhs, cond] = 
      Syntax.check_terms ctxt
        [(rewrite_lhs rewrite),
         (rewrite_rhs rewrite),
         (rewrite_cond rewrite)]
  in
    (lhs, rhs, cond)
  end

fun rewrite_to_term_param ctxt rewrite =
  let 
    val (lhs, rhs, cond) = type_checked_rewrites ctxt rewrite;
  in
    (ground_IRExpr ctxt lhs, ground_IRExpr ctxt rhs, ground_IRExpr ctxt cond)
  (*case (#rewrite rewrite) of
    Transform (lhs, rhs) => 
      ground_IRExpr ctxt lhs $ ground_IRExpr ctxt rhs
    | _ => raise TERM ("rewrite cannot be translated yet", [])*)
  end

fun generate ctxt term =
  let
    val (lhs, rhs, cond) = rewrite_to_term_param ctxt term;
    val generate_term = 
      (((Const ("TermRewrites.generate", @{typ "IRExpr \<Rightarrow> IRExpr \<Rightarrow> SideCondition \<Rightarrow> Rules"}))
      $ lhs) $ rhs) $ cond
    val value = Code_Evaluation.dynamic_value_strict ctxt generate_term;
  in              
    value
  end

fun code_of ctxt rewrite =
  @{const Trueprop} 
  $ ((Const ("HOL.eq", @{typ "Rules \<Rightarrow> Rules \<Rightarrow> bool"})
  $ (Free ((Binding.name_of (#name rewrite)) ^ "_code", @{typ "Rules"}))
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

fun rewrite_cmd ((bind: binding, options), opt) ctxt = 
  let
    val name = Binding.name_of bind;
    val _ = (if valid_name name then () 
             else (warning "Optimization name should be UpperCase not snake_case or camelCase"));
    val intval = case options of [[token]] => Token.content_of token = "intval" | _ => false;

    val subgoals = case options of [[token]] => Token.content_of token = "subgoals" | _ => false;
    val raw_term = (Syntax.parse_term ctxt opt);

    val term = IRExprMarkup.markup_expr [] ctxt [raw_term];
    val rewrite = of_term bind term raw_term;

    val ctxt = (if subgoals then
      (Specification.abbreviation (Syntax.mode_default)
        NONE []
        (val_def_const ctxt (#name rewrite) raw_term)
        false ctxt)
        (*((Binding.prefix_name "val_" bind, []), value_def ctxt (#name rewrite) raw_term) ctxt)*)
      else ctxt);

    (*val ctxt = (if subgoals then
      snd (Specification.definition
        NONE [] []
        ((Binding.prefix_name "val_" bind, []), value_def ctxt (#name rewrite) raw_term) ctxt)
      else ctxt);*)

    (*val ctxt = (if subgoals then
      (Specification.abbreviation (Syntax.mode_default)
        NONE []
        (word_def ctxt (#name rewrite) raw_term)
        false ctxt)
      else ctxt);*)

    val intval_preservation = (if intval 
      then intval_of ctxt (IntValMarkup.markup_expr [term] ctxt [(Syntax.parse_term ctxt opt)])
      else @{term True})
    val extra = (if intval then [(intval_preservation, [intval_preservation])] else [])

    val preservation = preservation_of ctxt rewrite;
    val preservation = if intval 
      then @{term "Pure.imp"} $ intval_preservation $ preservation
      else preservation;
    val termination = termination_of ctxt rewrite;
    val code = code_of ctxt rewrite;

    val register = fn proofs => RewritePhase.register (bind, (add_proofs rewrite proofs));

    fun after_qed thms lthy =
      let
        val lthy' = Local_Theory.background_theory (register (hd thms)) lthy;

        val (_, lthy'') = Specification.definition
            NONE [] []
            ((Binding.suffix_name "_code" bind, []), code)
            lthy'
      in
        snd (Local_Theory.note ((bind, []), hd thms) lthy'')
      end

    val target = (Proof.theorem NONE after_qed 
        [extra @ [(preservation, [preservation]), (termination, [termination])]] ctxt);

    val apply = (Proof.apply 
      ((Method.Source (Token.make_src ("unfold_optimization", Position.start) [])),
        Position.no_range) target);

    val result = (case Seq.hd apply of
       Seq.Result r => r
       | Seq.Error _ => target);

    val apply = (Proof.apply
      ((Method.Source (Token.make_src ("unfold_size", Position.start) [])),
       Position.no_range) (Proof.defer 1 result));

    val result = (case Seq.hd apply of
       Seq.Result r => r
       | Seq.Error _ => result);
  in
    result
  end

end