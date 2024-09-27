section Snipping

theory Snipping
  imports Main
  keywords
    "snipbegin" :: document_heading and
    "snipend" :: document_heading
begin

text \<open>Snippets allow specific components of the LaTeX document preparation to be included in other documents.\<close>

ML \<open>
(*
I thought the document_command was what generated the LaTeX output,
however, it appears to be hard-coded which makes this a bit of a hack.
*)
fun wrapped_command (command: string) (name: string option) =
  let
    val command = "\\" ^ command
    val argument = case name of
      NONE => "" |
      SOME v => ("{" ^ v ^ "}")
    val latex = (command ^ argument)
    val _ = @{print} latex;
  in
    Document_Output.document_output
        {markdown = false,            
         markup = fn _ => XML.enclose "%\n" "\n" (Latex.string latex)}
    (*(Pure_Syn.document_command {markdown = false} (NONE, doc))*)
  end

val _ =
  Outer_Syntax.command ("snipbegin", \<^here>) "start a snippet"
    (Parse.opt_target -- Parse.document_source >>
     (fn (opt, n) => 
      wrapped_command "isamarkupsnipbegin" (SOME (Input.string_of n)) (opt, n)));

val _ =
  Outer_Syntax.command ("snipend", \<^here>) "finish a snippet"
    (Parse.opt_target -- Parse.document_source >>
      (fn (opt, n) =>
        wrapped_command "isamarkupsnipend" (NONE) (opt, n)));
\<close>

(*
text \<open>
To use snippets, in your LaTeX preamble,
replace the command \verb|\isamarkupsnipbegin| with the start of a snippet,
and replace \verb|\isamarkupsnipend| with the end of a snippet.

By default snippets are placed into tcolorboxes.
\<close>

text_raw \<open>
\verbatim
\newcommand{\isamarkupsnipbegin}[1]{\begin{tcolorbox}[title=#1]}
\newcommand{\isamarkupsnipend}[1]{\end{tcolorbox}}
\end{verbatim}
\<close>
*)

(*text_raw \<open>
\newcommand{\isamarkupsnipbegin}[1]{\begin{tcolorbox}[title=#1]}
\newcommand{\isamarkupsnipend}[1]{\end{tcolorbox}}
\<close>*)


text \<open>
Snippets should be enclosed within the @{command snipbegin} and @{command snipend} commands.

For example, the box below is produced by the following:
\<close>

text \<open>
@{command snipbegin} ``snip-example''

@{command text} ``Hello world!''

@{command snipend}
\<close>

(*translations
  "\<^latex>\<open>\\index{\<close>v\<^latex>\<open>}\<close>v" <= "v"
*)

snipbegin \<open>snip-example\<close>

text \<open>Hello world!\<close>

ML \<open> Markup.document_latex\<close>
(*
lemma
  "1 + 1 = Suc (Suc 0)"
*)

snipend -

end