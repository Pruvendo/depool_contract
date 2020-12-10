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
| name :: "[" :: "]" :: t => ("М_"++name)%string :: concat_sq_brakets t
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
| "bytes"   => "I8"
| "bool"    => "B"
| "mapping" => "HM"
| "address" => "A"
| "TvmCell" => "C"
| _ => ("ι_" ++ t)%string
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















