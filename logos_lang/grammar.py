LOGOS_GRAMMAR = r"""
    start: statement*

    // --- LITURGY (Statements) ---
    statement: "proclaim" expr ";"                                   -> proclaim
             | "inscribe" NAME (":" NAME)? "=" expr ";"              -> inscribe
             | "amend" mutable "=" expr ";"                          -> amend
             | "apocrypha" STRING "mystery" NAME "(" params? ")" ("->" NAME)? ";" -> apocrypha
             | "tradition" STRING ("as" NAME)? ";"                  -> tradition
             | "chant" expr block "amen"                             -> chant
             | "discern" "(" expr ")" block "otherwise" block "amen" -> discernment
             | "vigil" block "confess" NAME block "amen"             -> vigil
             | "mystery" NAME "(" params? ")" ("->" NAME)? block "amen" -> mystery_def
             | "icon" NAME "{" field_decl* "}" "amen"                -> icon_def
             | "contemplate" "(" expr ")" "{" case_clause+ "}" "amen" -> contemplation
             | "offer" expr ";"                                      -> offer
             | "silence" ";"                                         -> silence
             | expr ";"                                              -> expr_stmt

    block: "{" statement* "}"                                        -> block

    field_decl: NAME ":" NAME ";"
    params: param ("," param)*
    param: NAME (":" NAME)?

    case_clause: "aspect" pattern ":" case_body
    ?case_body: block | statement
    ?pattern: "_" -> wildcard | expr

    ?expr: equality
    ?equality: comparison
             | equality "is" comparison               -> eq
             | equality "is" "not" comparison         -> ne

    ?comparison: sum
               | comparison "<" sum  -> lt
               | comparison ">" sum  -> gt
               | comparison "<=" sum -> le
               | comparison ">=" sum -> ge

    ?sum: product
        | sum "+" product -> add
        | sum "-" product -> sub

    ?product: unary
            | product "*" unary -> mul
            | product "/" unary -> div

    ?unary: "-" unary                          -> neg
          | call
          | "transfigure" expr "into" NAME     -> transfigure
          | "supplicate" expr                  -> supplicate

    ?call: access
         | NAME "(" args? ")" -> call

    ?access: atom
            | access "." NAME        -> get_attr
            | access "[" expr "]"    -> get_item

    ?mutable: NAME                  -> mut_var
             | mutable "." NAME      -> mut_attr
             | mutable "[" expr "]"  -> mut_item

    args: expr ("," expr)*

    atom: NUMBER  -> number
        | STRING  -> string
        | "Verily" -> verily
        | "Nay"    -> nay
        | "[" (expr ("," expr)*)? "]"        -> procession
        | "write" NAME "{" assign_list? "}" -> write_icon
        | NAME    -> var
        | "(" expr ")"

    assign_list: assign ("," assign)* ","?
    assign: NAME "=" expr

    NAME: /[a-zA-Z_]\w*/
    STRING: /"[^"\n]*"/
    NUMBER: /\d+(\.\d+)?/

    %import common.WS
    %ignore WS
    %ignore /#.*/
    %ignore /\/\/.*/
"""
