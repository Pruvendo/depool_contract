Fixpoint find_brace_interior (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "{" :: t => "{" :: find_brace_interior (n+1) t
| "}" :: t => if (Z.eqb n  0%Z) then "}" :: nil
                        else "}" :: find_brace_interior (n-1) t
| "" :: t => find_brace_interior n t
| h :: t => if (Z.eqb n (-1)%Z) then find_brace_interior n t
                             else h :: find_brace_interior n t 
end.
Fixpoint find_braket_interior (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "(" :: t => "(" :: find_braket_interior (n+1) t
| ")" :: t => if (Z.eqb n  0%Z) then ")" :: nil
                        else ")" :: find_braket_interior (n-1) t
| "" :: t => find_braket_interior n t
| h :: t => if (Z.eqb n (-1)%Z) then find_braket_interior n t
                             else h :: find_braket_interior n t 
end.
Fixpoint find_sq_braket_interior (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "[" :: t => "[" :: find_sq_braket_interior (n+1) t
| "]" :: t => if (Z.eqb n  0%Z) then "]" :: nil
                        else "]" :: find_sq_braket_interior (n-1) t
| "" :: t => find_sq_braket_interior n t
| h :: t => if (Z.eqb n (-1)%Z) then find_sq_braket_interior n t
                             else h :: find_sq_braket_interior n t 
end.
(* get lines between arguments and brace *)
Fixpoint find_crotch_interior (f:bool) (sl:list string) :=
match f, sl with
| _, nil => nil
| false, ")" :: t => find_crotch_interior true t
| true,  "{" :: t => nil
| true,   h  :: t => h :: (find_crotch_interior true t) 
| false,  h  :: t => find_crotch_interior true t
end.





