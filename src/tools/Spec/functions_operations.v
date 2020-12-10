Definition work_with_operations_tst(a b s c d : string) :=
 (* a :: "." :: b :: s :: c :: "." :: d :: t =>  *)
           "{(" ::  match who a, who c with
                    | NUMBER, _ => nil
                    | _, NUMBER => nil
                    | LOCAL, LOCAL => 
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | LOCAL, VAR =>
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
"(" :: "<-v"  :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, VAR => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                   end ++ [")}"].
                 
Definition work_with_operations_ts(a b s d : string) :=
 (* a :: "." :: b :: s :: d :: t =>  *)
           "{(" ::  match who a, who d with
                    | NUMBER, _ => nil
                    | LOCAL, NUMBER => 
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: d :: ["in"]
                    | LOCAL, LOCAL => 
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: d :: ["in"]
                    | LOCAL, VAR =>
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, LOCAL => 
"(" :: "<-v"  :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: d :: ["in"]
                    | VAR, VAR => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                   end ++ [")}"].

Definition work_with_operations_st(a s c d : string) :=
(* a :: s :: c :: "." :: d :: t =>  *)
           "{(" ::  match who a, who c with
                    | NUMBER, NUMBER => nil
                    | NUMBER, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | NUMBER, VAR =>
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | LOCAL, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | LOCAL, VAR =>
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | VAR, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
"(" :: "<-v"  :: a :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, VAR => 
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                   end ++ [")}"] .
Definition work_with_operations_s(a s b : string) :=
(* a :: s :: b *)
            "{(" :: match who a, who b with
                    | NUMBER, NUMBER => "let" :: "tt" :: ":=" :: a :: s :: b :: ["in"]
                    | NUMBER, LOCAL  => "let" :: "tt" :: ":=" :: a :: s :: b :: ["in"]
                    | NUMBER, VAR => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: a :: s :: ["in"]
                    | LOCAL, NUMBER => "let" :: a :: ":=" :: a :: s :: b :: ["in"]
                    | LOCAL, LOCAL  => "let" :: a :: ":=" :: a :: s :: b :: ["in"]
                    | LOCAL, VAR    => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: "tt" :: s :: a :: ["in"]
                    | VAR, NUMBER   => 
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: "tt" :: s :: b :: ["in"]
                    | VAR, LOCAL    =>
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: "tt" :: s :: b :: ["in"]
                    | VAR, VAR      => 
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" :: 
                                              "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                    end ++ [")}"].





Definition work_with_compares_tst(a b s c d : string) :=
 (* a :: "." :: b :: s :: c :: "." :: d :: t =>  *)
           "{[" ::  match who a, who c with
                    | NUMBER, _ => nil
                    | _, NUMBER => nil
                    | LOCAL, LOCAL => 
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | LOCAL, VAR =>
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
"(" :: "<-v"  :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, VAR => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                   end ++ ["]}"].
                 
Definition work_with_compares_ts(a b s d : string) :=
 (* a :: "." :: b :: s :: d :: t =>  *)
           "{[" ::  match who a, who d with
                    | NUMBER, _ => nil
                    | LOCAL, NUMBER => 
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: d :: ["in"]
                    | LOCAL, LOCAL => 
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: d :: ["in"]
                    | LOCAL, VAR =>
"(" :: "<-^l" :: a :: "^^" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, LOCAL => 
"(" :: "<-v"  :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: d :: ["in"]
                    | VAR, VAR => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                   end ++ ["]}"].

Definition work_with_compares_st(a s c d : string) :=
(* a :: s :: c :: "." :: d :: t =>  *)
           "{[" ::  match who a, who c with
                    | NUMBER, NUMBER => nil
                    | NUMBER, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | NUMBER, VAR =>
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | LOCAL, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | LOCAL, VAR =>
"(" :: "<-v"  :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: a :: s :: "tt2" :: ["in"]
                    | VAR, LOCAL => 
"(" :: "<-^l" :: c :: "^^" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
"(" :: "<-v"  :: a :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | VAR, VAR => 
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: d :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" ::
                                       "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                   end ++ ["]}"] .
Definition work_with_compares_s(a s b : string) :=
(* a :: s :: b *)
            "{[" :: match who a, who b with
                    | NUMBER, NUMBER => "let" :: "tt" :: ":=" :: a :: s :: b :: ["in"]
                    | NUMBER, LOCAL  => "let" :: "tt" :: ":=" :: a :: s :: b :: ["in"]
                    | NUMBER, VAR => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: a :: s :: ["in"]
                    | LOCAL, NUMBER => "let" :: "tt" :: ":=" :: a :: s :: b :: ["in"]
                    | LOCAL, LOCAL  => "let" :: "tt" :: ":=" :: a :: s :: b :: ["in"]
                    | LOCAL, VAR    => 
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: "tt" :: s :: a :: ["in"]
                    | VAR, NUMBER   => 
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: "tt" :: s :: b :: ["in"]
                    | VAR, LOCAL    =>
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt" :: "in" :: "let" :: "tt" :: ":=" :: "tt" :: s :: b :: ["in"]
                    | VAR, VAR      => 
"(" :: "<-v" :: a :: ")" :: ">>=" :: "->l" :: "tt1" :: "in" ::
"(" :: "<-v" :: b :: ")" :: ">>=" :: "->l" :: "tt2" :: "in" :: 
                                              "let" :: "tt" :: ":=" :: "tt1" :: s :: "tt2" :: ["in"]
                    | _, _ => nil
                    end ++ ["]}"].
             (* minus-minus plus-plus *)
Definition work_with_mmpp_tsb(a b n s : string) :=
 (* a . b [ n ] ++ or --  *)
"{|" ::  match who a, who b with
      | NUMBER, _ => nil
      | _, NUMBER => nil
      | LOCAL, LOCAL => nil
      | LOCAL, VAR => "(" :: ("<-^lb"++s)%string :: a :: "^^" :: b :: "[#" :: n :: "#]" :: ["in"]
      | VAR, VAR =>   "(" :: ("<-vb"++s)%string   :: b :: "[#" :: n :: "#]" :: ["in"] 
      | _, _ => nil
      end ++ ["|}"].

Definition work_with_mmpp_ts(a b s : string) :=
 (* a . b ++ or --  *)
"{|" ::  match who a, who b with
      | NUMBER, _ => nil
      | _, NUMBER => nil
      | LOCAL, LOCAL => nil
      | LOCAL, VAR => "(" :: ("<-^l"++s)%string :: a :: "^^" :: b :: ["in"]
      | VAR, VAR =>   "(" :: ("<-v"++s)%string   :: b :: ["in"] 
      | _, _ => nil
      end ++ ["|}"].

Definition work_with_mmpp_sb(a n s : string) :=
 (* a [ n ] ++ or --  *)
"{|" ::  match who a with
      | NUMBER => nil
      | LOCAL => "(" :: ("<-lb"++s)%string :: a :: "[#" :: n :: "#]" :: ["in"]
      | VAR =>   "(" :: ("<-vb"++s)%string   :: a :: "[#" :: n :: "#]" :: ["in"] 
      | _  => nil
      end ++ ["|}"].

Definition work_with_mmpp_s(a s : string) :=
 (* a ++ or --  *)
"{|" ::  match who a with
      | NUMBER => "(" :: ("<-c"++s)%string :: a :: ")" :: ["in"]
      | LOCAL  => "(" :: ("<-l"++s)%string :: a :: ["in"]
      | VAR    => "(" :: ("<-v"++s)%string   :: a :: ["in"] 
      | _=> nil
      end ++ ["|}"].






Fixpoint work_with_operations(sl:list string) :=
match sl with
| nil => nil
| a :: "." :: b :: "+" :: c :: "." :: d :: t => (work_with_operations_tst a b "+" c d)++(work_with_operations t)
| a :: "." :: b :: "-" :: c :: "." :: d :: t => (work_with_operations_tst a b "-" c d)++(work_with_operations t)
| a :: "." :: b :: "*" :: c :: "." :: d :: t => (work_with_operations_tst a b "*" c d)++(work_with_operations t)
| a :: "." :: b :: "/" :: c :: "." :: d :: t => (work_with_operations_tst a b "/" c d)++(work_with_operations t)

| a :: "." :: b :: "+" :: d :: t =>  (work_with_operations_ts a b "+" d)++(work_with_operations t)
| a :: "." :: b :: "-" :: d :: t =>  (work_with_operations_ts a b "-" d)++(work_with_operations t)
| a :: "." :: b :: "*" :: d :: t =>  (work_with_operations_ts a b "*" d)++(work_with_operations t)
| a :: "." :: b :: "/" :: d :: t =>  (work_with_operations_ts a b "/" d)++(work_with_operations t)

| a :: "+" :: c :: "." :: d :: t => (work_with_operations_st a "+" c d)++(work_with_operations t)
| a :: "-" :: c :: "." :: d :: t => (work_with_operations_st a "-" c d)++(work_with_operations t)
| a :: "*" :: c :: "." :: d :: t => (work_with_operations_st a "*" c d)++(work_with_operations t)
| a :: "/" :: c :: "." :: d :: t => (work_with_operations_st a "/" c d)++(work_with_operations t)

| a :: "+" :: b :: t =>  (work_with_operations_s a "+" b )++(work_with_operations t)
| a :: "-" :: b :: t =>  (work_with_operations_s a "-" b )++(work_with_operations t)
| a :: "*" :: b :: t =>  (work_with_operations_s a "*" b )++(work_with_operations t)    
| a :: "/" :: b :: t =>  (work_with_operations_s a "/" b )++(work_with_operations t) 

| h :: t => h :: ( work_with_operations t )
end .

Fixpoint work_with_compares(sl:list string) :=
match sl with
| nil => nil
| a :: "." :: b :: ">" :: c :: "." :: d :: t => (work_with_compares_tst a b ">" c d)++(work_with_compares t)
| a :: "." :: b :: "<" :: c :: "." :: d :: t => (work_with_compares_tst a b "<" c d)++(work_with_compares t)
| a :: "." :: b :: ">=" :: c :: "." :: d :: t => (work_with_compares_tst a b ">=" c d)++(work_with_compares t)
| a :: "." :: b :: "<=" :: c :: "." :: d :: t => (work_with_compares_tst a b "<=" c d)++(work_with_compares t)
| a :: "." :: b :: "==" :: c :: "." :: d :: t => (work_with_compares_tst a b "==" c d)++(work_with_compares t)
| a :: "." :: b :: "!=" :: c :: "." :: d :: t => (work_with_compares_tst a b "!=" c d)++(work_with_compares t)

| a :: "." :: b :: ">" :: d :: t =>  (work_with_compares_ts a b ">" d)++(work_with_compares t)
| a :: "." :: b :: "<" :: d :: t =>  (work_with_compares_ts a b "<" d)++(work_with_compares t)
| a :: "." :: b :: ">=" :: d :: t =>  (work_with_compares_ts a b ">=" d)++(work_with_compares t)
| a :: "." :: b :: "<=" :: d :: t =>  (work_with_compares_ts a b "<=" d)++(work_with_compares t)
| a :: "." :: b :: "==" :: d :: t =>  (work_with_compares_ts a b "==" d)++(work_with_compares t)
| a :: "." :: b :: "!=" :: d :: t =>  (work_with_compares_ts a b "!=" d)++(work_with_compares t)

| a :: ">" :: c :: "." :: d :: t => (work_with_compares_st a ">" c d)++(work_with_compares t)
| a :: "<" :: c :: "." :: d :: t => (work_with_compares_st a "<" c d)++(work_with_compares t)
| a :: ">=" :: c :: "." :: d :: t => (work_with_compares_st a ">=" c d)++(work_with_compares t)
| a :: "<=" :: c :: "." :: d :: t => (work_with_compares_st a "<=" c d)++(work_with_compares t)
| a :: "==" :: c :: "." :: d :: t => (work_with_compares_st a "==" c d)++(work_with_compares t)
| a :: "!=" :: c :: "." :: d :: t => (work_with_compares_st a "!=" c d)++(work_with_compares t)

| a :: ">" :: b :: t =>  (work_with_compares_s a ">" b )++(work_with_compares t)
| a :: "<" :: b :: t =>  (work_with_compares_s a "<" b )++(work_with_compares t)
| a :: ">=" :: b :: t =>  (work_with_compares_s a ">=" b )++(work_with_compares t)    
| a :: "<=" :: b :: t =>  (work_with_compares_s a "<=" b )++(work_with_compares t) 
| a :: "==" :: b :: t =>  (work_with_compares_s a "==" b )++(work_with_compares t)    
| a :: "!=" :: b :: t =>  (work_with_compares_s a "!=" b )++(work_with_compares t) 

| h :: t => h :: ( work_with_compares t )
end .
(* ++ and -- *)
Fixpoint work_with_mmpp(sl:list string) :=
match sl with
| nil => nil
| a :: "." :: b :: "[" :: n :: "]" :: "++" :: t => (work_with_mmpp_tsb a b n "++")++(work_with_mmpp t)
| a :: "." :: b :: "[" :: n :: "]" :: "--" :: t => (work_with_mmpp_tsb a b n "--")++(work_with_mmpp t)
| a :: "." :: b :: "++" :: t => (work_with_mmpp_ts a b "++")++(work_with_mmpp t)
| a :: "." :: b :: "--" :: t => (work_with_mmpp_ts a b "--")++(work_with_mmpp t)
| a :: "[" :: n :: "]" :: "++" :: t => (work_with_mmpp_sb a n "++")++(work_with_mmpp t)
| a :: "[" :: n :: "]" :: "--" :: t => (work_with_mmpp_sb a n "--")++(work_with_mmpp t)
| a :: "++" :: t => (work_with_mmpp_s a "++")++(work_with_mmpp t)
| a :: "--" :: t => (work_with_mmpp_s a "--")++(work_with_mmpp t)

| h :: t => h :: ( work_with_mmpp t )
end .

Fixpoint work_with_operations'(sl:list string) :=
match sl with
| nil => nil
| h :: t => if( (headS "" t) =? "{") then let q := find_brace_interior (-1) t in
                                          let qq := last_delete (tail q) in
                                        ( work_with_operations qq )
                                     else h :: (work_with_operations' t)
end.

Compute (let q := "Definition ElectionParams_Ф__getFreezingPeriod  :=  { return ElectionParams_ι_m_electedFor >= ElectionParams_ι_m_heldFor ; }" in 
let t := clear_string_easy (split_string' " " q) in concat_with " " (work_with_compares t)).

Fixpoint work_with_let(f:bool)(acc sl:list string) :=
match f, sl with
| _, nil => nil
| _, "require" :: "(" :: t => "require" :: "(" :: (work_with_let false [] t)
| false, "(" :: h :: "," :: t => work_with_let true ("(" :: h :: "," :: nil) t
| true, h :: ")" :: "=" :: t => "letN" :: acc ++ h :: ")" :: ":=" :: work_with_let false [] t
| true, h :: ")" :: t => acc ++ h :: ")" :: work_with_let false [] t
| true, h :: "," :: t => work_with_let true (acc++h :: [","]) t
| false, h :: t => h :: (work_with_let false [] t)
| true, h :: t =>  work_with_let true acc t
end.

Fixpoint work_with_structConstr(f:bool)(acc ls sl:list string) :=
match f, sl with
| _, nil => nil
| _, "require" :: "(" :: t => "require" :: "(" :: (work_with_structConstr false [] ls t)
| false, h :: "(" :: h' :: "," :: t =>  if(test_already_exists h ls) 
                                       then 
               work_with_structConstr true ("("::(h++"C")%string :: h' :: nil) ls t
                                       else 
               h :: "(" :: h' :: "," :: (work_with_structConstr false [] ls t)
| true, h :: ")" :: t => acc ++ h :: ")" :: ">>" :: work_with_structConstr false [] ls t
| true, h :: "," :: t => work_with_structConstr true (acc++h :: nil) ls t
| false, h :: t => h :: (work_with_structConstr false [] ls t)
| true, h :: t =>  work_with_structConstr true acc ls t
end.

Fixpoint concat_op_equ(sl:list string) :=
match sl with
| nil => nil
| "+" :: "=" :: t => "+=" :: (concat_op_equ t)
| "-" :: "=" :: t => "-=" :: (concat_op_equ t)
| "/" :: "=" :: t => "/=" :: (concat_op_equ t)
| "*" :: "=" :: t => "*=" :: (concat_op_equ t)
| "+" :: "+" :: t => "++" :: (concat_op_equ t)
| "-" :: "-" :: t => "--" :: (concat_op_equ t)
| "&" :: "&" :: t => "&&" :: (concat_op_equ t)
| "|" :: "|" :: t => "||" :: (concat_op_equ t)
| "!" :: "=" :: t => "!=" :: (concat_op_equ t)
| "address" :: "(" :: n :: ")" :: t => ("address"++"("++n++")")%string :: (concat_op_equ t) 
| "msg" :: "." :: "sender" :: "." :: "transfer" :: t => 
              ("msg"++"."++"sender"++"."++"transfer")%string :: (concat_op_equ t) 
| "msg" :: "." :: "value" :: t => ("msg"++"."++"value")%string :: (concat_op_equ t) 
| "msg" :: "." :: "sender" :: t => 
              ("msg"++"."++"sender")%string :: (concat_op_equ t) 

| h :: t => h :: (concat_op_equ t)
end.
(* i.e.  a == b  to ( xIntEqb a b ) *)
Fixpoint compare_to_coq_mode (sl:list string) :=
match sl with
| nil => nil
| a :: "==" :: b :: t => "(" :: "xIntEqb" :: a :: b :: ")" :: compare_to_coq_mode t
| a :: ">=" :: b :: t => "(" :: "xIntGeb" :: a :: b :: ")" :: compare_to_coq_mode t
| a :: "<=" :: b :: t => "(" :: "xIntLeb" :: a :: b :: ")" :: compare_to_coq_mode t
| a :: ">" :: b :: t => "(" :: "xIntGtb" :: a :: b :: ")" :: compare_to_coq_mode t
| a :: "<" :: b :: t => "(" :: "xIntLtb" :: a :: b :: ")" :: compare_to_coq_mode t
| a :: "!=" :: b :: t => "(" :: "boolNegb" :: "(" :: "xIntEqb" :: a :: b :: ")" :: ")" :: compare_to_coq_mode t
| "!" :: a :: t => "(" :: "boolNegb" :: a :: ")" :: compare_to_coq_mode t
| h :: t => h :: compare_to_coq_mode t
end.
(* i.e. a + b to ( xIntPlus a b ) *)
Fixpoint opers_to_coq_mode (sl:list string) :=
match sl with
| nil => nil
| a :: "+" :: b :: t => "(" :: "xIntPlus" :: a :: b :: ")" :: opers_to_coq_mode t
| a :: "-" :: b :: t => "(" :: "xIntMinus" :: a :: b :: ")" :: opers_to_coq_mode t
| a :: "*" :: b :: t => "(" :: "xIntMult" :: a :: b :: ")" :: opers_to_coq_mode t
| a :: "/" :: b :: t => "(" :: "xIntDiv" :: a :: b :: ")" :: opers_to_coq_mode t
| a :: "^" :: b :: t => "(" :: "xIntPow" :: a :: b :: ")" :: opers_to_coq_mode t

| h :: t => h :: opers_to_coq_mode t
end.













