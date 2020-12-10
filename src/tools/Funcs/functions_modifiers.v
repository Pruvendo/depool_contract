(* Working with modifiers mmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm *)
Definition make_modifier_interior (modifier_name:string) (sl:list string) :=
let braket := find_braket_interior (-1) sl in
let brace  := find_brace_interior (-1) sl in
let x := "Modifier" :: modifier_name
               :: braket ++ last_delete ( List.tail brace ) in   x.
Definition get_modifier (contract_name:string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let modifier_name := 
     (contract_name++"_ι_"++h)%string in make_modifier_interior modifier_name sl
end.
Fixpoint make_modifiers (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "modifier" :: t => (get_modifier contract_name t) :: (make_modifiers contract_name t)
| h :: t => make_modifiers contract_name t
end.















Fixpoint get_require_body(f:bool)(sl:list string) :=
match f, sl with
| _, nil => nil
| _, ";" :: t => [";"]
| false, "require" :: t => "require" :: (get_require_body true t)
| true, h :: t => h :: (get_require_body true t)
| false, h :: t => (get_require_body true t)
end.
Definition get_list_modifier (name:string)(sl:list string) :=
let q := find_brace_interior (-1) sl in
let w := last_delete (tail q) in
let e := get_require_body false w in                        (name, e).

Fixpoint modifier_list_with_bodies (sl:list string) :=
match sl with
| nil => nil
| "modifier" :: name :: t => (get_list_modifier name t) :: (modifier_list_with_bodies t)
| h :: t => (modifier_list_with_bodies t)
end.




