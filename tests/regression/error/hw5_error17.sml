val prog =
  PROGRAM
    {classes=[],decls=[],
     funcs=[("f",
             {body=[ST_PRINT {exp=EXP_ID "a"},ST_PRINT {exp=EXP_STRING "\n"},
                    ST_PRINT {exp=EXP_ID "a"},ST_PRINT {exp=EXP_STRING "\n"}],
              decls=[],params=["a","a"]})],
     stmts=[ST_EXP {exp=EXP_CALL {args=[EXP_NUM 1,EXP_NUM 2],func=EXP_ID "f"}}]}
  : program
;
