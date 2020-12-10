(* Work with structs ssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss*)
Definition make_struct_interior (struct_name:string) (sl:list string) :=
let x := find_brace_interior (-1) sl in
let x := last_delete ( List.tail x ) in   x.
Definition get_name_from_type_string(s:string) :=
     headS "" (split_string' " " s).
Definition make_line_for_Global_Instatce(s:string):=
match s with
| "" => ""
| "{" => ""
| "}" => ""
| " " => ""
| String "010"%char "" => ""
| String "010"%char " " => ""
| String " "%char (String "010"%char "") => ""
| String "010"%char (String "010"%char "") => ""
| _ => (tab++tab++"@existT _ _ _ "++(get_name_from_type_string s)++",")%string
end.
Fixpoint clear_some_symbols(s:string) :=
match s with
| "" => ""
| String "{"%char t => clear_some_symbols t
| String "}"%char t => clear_some_symbols t
| String "."%char t => clear_some_symbols t
| String "009"%char t => clear_some_symbols t
| String "010"%char t => clear_some_symbols t
| String h t => String h (clear_some_symbols t)
end.
 
Fixpoint make_pull_up_per_number(n:nat)(sl:list string) :=
match sl with
| nil => nil
| h :: t => let x := split_string' " "  h in let y := clear_some_symbols (headS "" x)
                                                        in match y with
                                                           | "" => make_pull_up_per_number n t
                        | String newline " " => make_pull_up_per_number n t
                                                           | _ =>
  ("Global Instance Acc_"++y++" : Accessor "++y++" := { acc := ·"++(writeNat n)++" } ."++newline)%string ::
                                make_pull_up_per_number (S n) t
                                                           end 
end.
 
Definition get_struct_itself(struct_name:string) (sl:list string) :=
match sl with                                             
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in  
            let x := get_type_lines struct_name x in x
end.
Fixpoint list_pass (l:list string) :=
match l with
| nil => ""
| "{
" :: t   => list_pass t
| "}.
" :: t  => list_pass t
| h :: t => if (isEmpty h) then list_pass t
                           else ("default" ++ " " ++ (list_pass t))%string
end.

Definition get_struct_var_list (contract_name:string) (sl:list string) :=
match sl with                                               (* get_type_list *)
| nil => nil
| h :: t => let struct_name := (contract_name++"_ι_"++h)%string in 
           ( get_struct_itself struct_name sl )
end.
Fixpoint make_structs_var_list (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "struct" :: t => (get_struct_var_list contract_name t) :: (make_structs_var_list contract_name t)
| h :: t => make_structs_var_list contract_name t
end. 





