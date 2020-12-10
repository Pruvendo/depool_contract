Definition str2nat (s:string) :=
match s with
| "" => 0
| "0" => 0
| "1" => 1
| "2" => 2
| "3" => 3
| "4" => 4
| "5" => 5
| "6" => 6
| "7" => 7
| "8" => 8
| "9" => 9
| "A" => 10
| "B" => 11
| "C" => 12
| "D" => 13
| "E" => 14
| "F" => 15
| "a" => 10
| "b" => 11
| "c" => 12
| "d" => 13
| "e" => 14
| "f" => 15
| _ => 0
end.
Fixpoint setSpace (s:string) :=
match s with
| "" => "" 
| String "("%char t => String " "%char (String "("%char (String " "%char (setSpace t)))
| String "{"%char t => String " "%char (String "{"%char (String " "%char (setSpace t)))
| String "]"%char t => String " "%char (String "]"%char (String " "%char (setSpace t)))
| String ")"%char t => String " "%char (String ")"%char (String " "%char (setSpace t)))
| String "}"%char t => String " "%char (String "}"%char (String " "%char (setSpace t)))
| String "["%char t => String " "%char (String "["%char (String " "%char (setSpace t)))
| String ";"%char t => String " "%char (String ";"%char (String " "%char (setSpace t)))
| String ","%char t => String " "%char (String ","%char (String " "%char (setSpace t)))
| String "+"%char t => String " "%char (String "+"%char (String " "%char (setSpace t)))
| String "-"%char t => String " "%char (String "-"%char (String " "%char (setSpace t)))
| String "."%char t => String " "%char (String "."%char (String " "%char (setSpace t)))
| String "!"%char t => String " "%char (String "!"%char (String " "%char (setSpace t)))
| String ":"%char t => String " "%char (String ":"%char (String " "%char (setSpace t)))
(* | String "*"%char t => String " "%char (String "*"%char (String " "%char (setSpace t))) *)
| String "m"%char (String "s"%char (String "g"%char (String "."%char t))) =>
              String "m"%char (String "s"%char (String "g"%char (String "_"%char (setSpace t))))
| String "t"%char (String "v"%char (String "m"%char (String "."%char t))) =>
              String "t"%char (String "v"%char (String "m"%char (String "_"%char (setSpace t))))


| String h t => String h (setSpace t)
end.
(* type 'name[]' to 'М_name' *)
Fixpoint concat_sq_brakets (sl:list string) :=
match sl with
| nil => nil
| name :: "[" :: "]" :: t => ((* "М_"++ *)name)%string :: concat_sq_brakets t
| h :: t => h :: concat_sq_brakets t
end.

(*************************************************************************************************)
(*  solidity type to coq alias type  *)
Definition sol_types2coq_mini_types (t:string):=
match t with
| "" => ""
| "uint"    => "I"
| "uint8"   => "I8"
| "uint16"  => "I16"
| "uint32"  => "I32"
| "uint64"  => "I64"
| "uint128" => "I128"
| "uint256" => "I256"
| "int8"   => "I8"
| "int16"  => "I16"
| "int32"  => "I32"
| "int64"  => "I64"
| "int128" => "I128"
| "int256" => "I256"
| "bytes"   => "I8"
| "bool"    => "B"
| "mapping" => "HM"
| "address" => "A"
| "TvmCell" => "C"
| _ => ((* "ι_" ++ *) t)%string
end.
Definition del_lead_2_symbolsι_(s:string):=
match s with
| "" => ""
| String a (String b (String c t)) => t
| _ => s
end.
Compute (del_lead_2_symbolsι_ "Л_1234567").
(* Coq alias type to coq full type *)
Definition cot_mini_types2coq_types (t:string):=
match t with
| "" => ""
| "I" => "XInteger"
| "I8"   => "XInteger8"
| "I16"  => "XInteger16"
| "I32"  => "XInteger32"
| "I64"  => "XInteger64"
| "I128" => "XInteger128"
| "I256" => "XInteger256"
| "C"    => "TvmCell"
| "B"    => "XBool"
| "Arr"  => "XArray"
| "HM"   => "XHMap"
| "A" => "XAddress"
| _ =>  t
end.
Definition sol2coq_full_types(t:string):=cot_mini_types2coq_types (sol_types2coq_mini_types t).
(* Test for empty *)
Fixpoint isEmpty(s:string):bool :=
match s with
| "" => true
| String "010"%char t => isEmpty t
| String " "%char t => isEmpty t
| String "009"%char t => isEmpty t
| String "}"%char t => isEmpty t
| String "{"%char t => isEmpty t
| String ")"%char t => isEmpty t
| String "("%char t => isEmpty t
| String "]"%char t => isEmpty t
| String "["%char t => isEmpty t
| String ";"%char t => isEmpty t
| String ":"%char t => isEmpty t
| String "."%char t => isEmpty t

| String h t => false
end.

Fixpoint work_with_IProxy(sl:list string) :=
match sl with
| nil => nil
| "IProxy" :: "(" :: h1 :: ")" :: t => 
         match t with 
         | "." :: h2 :: "." :: t' => 
             match t' with
             | h3 :: "(" :: h4 :: ")" :: t'' =>
                   match t'' with
                   | "(" :: h5 :: ")" :: t''' => if(have_it_symbol "185"%char h5) 
                      then  
         "(" :: "<-v" :: h1 :: ")" :: ">>=" :: "->l" :: "ti1" :: "in" :: newline :: tab ::
         "(" :: "<-v" :: h4 :: ")" :: ">>=" :: "->l" :: "ti2" :: "in" :: newline :: tab ::
         "(" :: "<-v" :: h5 :: ")" :: ">>=" :: "->l" :: "ti3" :: "in" :: newline :: tab ::
         "IProxy" :: "(" :: "ti1" :: ")" :: "." :: h2 :: "." :: h3 :: "(" :: "ti2" :: ")" ::
                                                                     "(" :: "ti3" :: ")" :: t'''
                      else
         "(" :: "<-v" :: h1 :: ")" :: ">>=" :: "->l" :: "ti1" :: "in" :: newline :: tab ::
         "(" :: "<-v" :: h4 :: ")" :: ">>=" :: "->l" :: "ti2" :: "in" :: newline :: tab ::
         "IProxy" :: "(" :: "ti1" :: ")" :: "." :: h2 :: "." :: h3 :: "(" :: "ti2" :: ")" ::
                                                                    "(" :: h5 :: ")" :: t'''
 
                   | _ => 
      "IProxy" :: "(" :: h1 :: ")" :: "." :: h2 :: "." :: h3 :: "(" :: h4 :: ")" :: work_with_IProxy t''
                   end
             | _ => "IProxy" :: "(" :: h1 :: ")" :: "." :: h2 :: "." :: work_with_IProxy t'
             end
         | _ => "IProxy" :: "(" :: h1 :: ")" :: work_with_IProxy t
         end
| h :: t => h :: work_with_IProxy t
end.

Fixpoint all_end_prepare (sl:list string) :=
let fix tail' (sl:list string) := 
match sl with
| nil => nil
| "
" :: t => tail' t
| (String "009"%char "") :: t => tail' t
| " " :: t => tail' t
| "" :: t => tail' t
| h :: t => all_end_prepare t
end in 
match sl with
| nil => nil
| ":=" :: t => match what_is_next t with
              | "{" => ":=" :: newline :: tail' t
              | _   => ":=" :: all_end_prepare t
              end
| "}" :: t => match what_is_next t with
              | "Definition" => "." :: newline :: newline :: all_end_prepare t
              | "else" => "}" :: all_end_prepare t
              | "(" => "}" :: all_end_prepare t
              | _ => "}" :: ">>" :: all_end_prepare t
             end

| "return" :: "(" :: t => "return#" :: "(" :: all_end_prepare t
| "return" :: t => "return!" :: all_end_prepare t

| "now" :: t => "tvm_now" :: all_end_prepare t 

| "LedgerT" :: ":=" :: t => "LedgerT" :: "True" :: ":=" :: all_end_prepare t

| "LedgerT" :: h :: t => if ( have_it_symbol "226"%char h ) (* ↑ *)
                         then "LedgerT" :: all_end_prepare t 
                         else "LedgerT" :: h :: all_end_prepare t 

| "))" :: ">>" :: t => "))" :: ">>" :: all_end_prepare t
| "))" :: ":" :: t => ")" :: ":" :: all_end_prepare t
| "((" :: "," :: t => "((" :: "_" :: "," :: all_end_prepare t
| "," :: "," :: t => "," :: "_" :: "," :: all_end_prepare t
| "," :: "))" :: t => "," :: "_" :: "))" :: all_end_prepare t 
| h :: t => if ( ( first2 h ) =? "0x" )
            then match h with
                 | "" => "" :: all_end_prepare t
                 | String _ t' => ( String "O"%char t' ) :: all_end_prepare t
                 end
            else h :: all_end_prepare t
end.

Fixpoint prepare_easy_funcs (sl:list string) :=
match sl with
| nil => nil
| "True" :: ":=" :: t => let q := find_brace_interior (-1) t in (* [writeNat (List.length q)] *) 
               if ( Nat.ltb (List.length q) 5 ) 
               then "True" :: newline :: tab :: ":=" :: "return!" :: "I" :: ["."] 
               else ":=" :: prepare_easy_funcs t
| h :: t => h :: prepare_easy_funcs t
end.



Fixpoint string2list (s:string) :=
match s with
| "" => nil
| String h t => (String h "") :: string2list t
end.
Fixpoint get_hex2dec' (sl:list string) :=
match sl with
| nil => 0
| h :: t => ( str2nat h ) + 16 * ( get_hex2dec' t )
end.

Definition get_hex2dec (s:string) :=
let q := string2list s in
let w := tail ( tail q ) in (* remane '0x' *)
let e := List.rev w in
get_hex2dec' e.

Definition uppers := ["d0!";"d1!";"d2!";"d3!";"d4!";"d5!";"u0!";"u1!";"u2!";"u3!";"u4!";"u5!"].

Fixpoint dotted_prepare (sl:list string) :=
    let fix tail' (sl:list string) :=
    match sl with
    | nil => nil
    | h :: t => if (have_it_symbol "226"%char h) (* ↑ *)
                then dotted_prepare t
                else h :: dotted_prepare t
    end in
    let fix tail'' (sl:list string) :=
    match sl with
    | nil => nil
    | ")" :: t => "!)" :: dotted_prepare t
    | h :: t => h :: tail'' t
    end in
match sl with
| nil => nil
| "^^" :: h :: t => if ( test_already_exists h uppers ) 
                    then "^^" :: dotted_prepare t
                    else if (have_it_symbol "226"%char h) (* ↑ *)
                         then "^^" :: dotted_prepare t
                         else "^^" :: h :: dotted_prepare t

| ":=" :: "{" :: t => ":=" :: newline :: dotted_prepare t

| h :: "(" :: ")" :: t => h :: "()" :: dotted_prepare t

| h :: "(" :: t => if ( ( first4 h ) =? "tvm_" )
                   then h :: "(!" :: tail'' t 
                   else h :: "(" :: dotted_prepare t

| "$" :: "Л_cell" :: "^^" :: "toSlice" :: "(" :: ")" :: ">>" :: t =>
                "Л_cell" :: "->toSlice" :: "()" :: ">>" :: dotted_prepare t

| h :: t => if ( ( what_is_next t ) =? "" ) 
            then if ( h =? "." ) then [h] 
                                 else h :: "." :: [newline ; newline]
            else            (* test for     d0! ↑9 kjhsdf_ι_sdfsdf          *)
                 if ( test_already_exists h uppers )
                 then h :: tail' t
                 else h :: dotted_prepare t

end.


