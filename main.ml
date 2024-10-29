let char_list_of_string s = List.init (String.length s) (String.get s);;
let rec string_of_char_list = function
	| [] -> ""
	| c::q -> (String.make 1 c)^(string_of_char_list q)

let rec range (i:int) (j:int) : int list =
	if i < j then i::(range (i+1) j) else []
let char_range (i:int) (j:int) : char list =
	List.map Char.chr (range i j)
let range_char (c1:char)(c2:char) : char list =
	char_range (Char.code c1) (Char.code c2)

type ('a ,'b) automaton = {
	init_states: 'a list;
	end_states: 'a list;
	transitions: ('a*'b*'a) list
}

type ('a ,'b ,'c) determinist_automaton = {
	init_state: 'a ;
	ending_info: ('a,'c option) Hashtbl.t ;
	delta_htbl: (('a*'b), 'a) Hashtbl.t
}
(* Cas particuliers utiles : *)
type ('a, 'c) language_determinist_automaton = ('a , char, 'c) determinist_automaton
type 'a language_determinised_automaton = ('a list, 'a) language_determinist_automaton
type regex_det_auto = int language_determinised_automaton

type capture_positions = (int*int) list 

type 'a local_language = {
	l: bool;
	p: 'a list;
	s: 'a list;
	f: ('a*'a) list
}

type 'a local = (bool) * ('a list) * ('a list) * ( ('a*'a) list )

type 'a reg = 
	| Letter of 'a
	| Joker of (char list )*int
	| Or of 'a reg * 'a reg 
	| Optional of 'a reg
	| Repeat of 'a reg
	| Concat of 'a reg * 'a reg
	| Epsilon

type state = char*int;;

let linearise (regex : 'a list ) : ('a*int) list =
	let rec aux (n:int) : 'a list -> ('a*int) list = function
		| [] -> []
		| c::q -> (c, n)::(aux (n+1) q)
	in
	aux 0 regex
;;

let rec transitions_two_factors (f : ('a*'a) list ) : ('a*'a*'a) list = match f with  
	| [] -> []
	| (a1, a2)::q -> (a1, a2, a2)::(transitions_two_factors q)

let automaton_of_local_language (loc : 'a local_language) : ('a option, 'a) automaton =
	let end_states = List.map (fun x -> Some x) loc.s in  
	{
		init_states = [None]; 
		end_states = if loc.l then None::end_states else end_states; 
		transitions = (List.map (fun x-> (None, x, Some x)) loc.p) @
		List.map (fun (a,b,c) -> (Some a, b, Some c)) (transitions_two_factors loc.f)
	}

let rec concat_list : ('a reg) list -> 'a reg  = function
	| [] -> Epsilon
	| a::q -> Concat (a, (concat_list q))

let special_chars : char list = ['('; ')'; '|'; '?';'+';'*';'\\';'.']

let regex_of_text (t : (char*int) list) : (char*int) reg   =
	let rec aux res or_content on_going = function
	| (')', n)::q -> (concat_list [res; or_content; on_going], (')', n)::q)
	| ('(', n)::q -> begin
		match aux res Epsilon Epsilon q with 
		| (reg1, (')', _)::q') -> aux res (Concat(or_content,on_going)) reg1 q' 
		| _ -> failwith ("Parentheses at position "^string_of_int n ^ " is not closed ")
	end
	| ('|', _)::q -> let (reg1, q') = aux Epsilon Epsilon Epsilon q in aux res (Or(Concat(or_content,on_going),reg1)) Epsilon q'
	| ('?', _)::q -> aux res or_content (Optional on_going) q
	| ('+', _)::q -> aux res or_content (Repeat on_going) q
	| ('*', _)::q -> aux res or_content (Optional (Repeat on_going)) q
	| ('.', n)::q -> aux res (Concat(or_content,on_going)) (Joker ((char_range 0 256) , n) ) q
	| ('[', n)::q -> let rec get_inside_brackets l =
						match l with 
							| [] -> failwith ("bracket [ at postion "^(string_of_int n)^" not closed")
							| ('\\', _)::[] -> failwith ("bracket [ at postion "^(string_of_int n)^" not closed and string ended with backslash")
							| ('\\', _)::(c , m)::q -> if List.mem c ['[';']';'-'] 
														then let (s,q2) = get_inside_brackets q in ((Some c,m)::s, q2)
														else failwith ("Connot escape inside square brackets : "^(String.make 1 c)^" at position "^(string_of_int n)^" ( only [,],- can ) ")
							| ('-', m)::q -> let (s,q2) = get_inside_brackets q in ((None,m)::s, q2)
							| ('[', m)::q -> failwith ("In brackets : cannot open '[' a second time at position "^(string_of_int m)^" ( already opened at position : "^(string_of_int n)^").\n Did you forget to escape it or to close the previous one ?")
							| (']', _)::q -> ([], q)
							| (c,m)::q -> let (s,q2) = get_inside_brackets q in ((Some c,m)::s, q2)
						in 
						let rec get_char_set l = 
							match l with 
								| [] -> []
								| (Some c1,_)::(None,m)::(Some c2,_)::q -> let r = (range_char c1 c2) in begin 
									(if r = [] then print_string ("Warning : "^(String.make 1 c1)^" and "^(String.make 1 c2)^" around position "^(string_of_int m)^" are at reverse order so they are useless !\n" ) else () );
									r@(get_char_set q)
								end
								| (None, m)::q -> failwith ("In brackets : the '-' at postion "^(string_of_int(-m-1))^" should be associated with two neighours, you can't begin with '-' nor have 'a-b-c'")
								| (Some c,_)::q ->  c::(get_char_set q)
						in 
						let ( l , q') = get_inside_brackets q in 
						let cs = get_char_set l in 
						aux res (Concat(or_content,on_going)) (Joker (cs , n) ) q'

	| ('\\', _)::(ch,n)::q -> 
		if not (List.mem ch special_chars) then 
		failwith ("Cannot escape non special character : '"^(String.make 1 ch)^"' at position "^(string_of_int n) )
		else aux res (Concat(or_content,on_going)) (Letter (ch,n)) q
	| (ch,n)::q -> if ch = '\\' then failwith "Cannot end the string with backslash, backslash has to escape something !"
	else aux res (Concat(or_content,on_going)) (Letter (ch,n)) q
	| [] -> (concat_list [res; or_content; on_going], [])
	in 
	match aux Epsilon Epsilon Epsilon t with 
		| (reg, []) -> reg
		| (_ , (a,n)::_) -> failwith ("unexpected "^(String.make 1 a)^" at postion "^string_of_int n)
	

let rec simplify_regex (reg : 'a reg) : 'a reg =
	match reg with 
	| Letter _ | Joker _ -> reg 
	| Or (a,b) -> begin
		let (a',b') = (simplify_regex a, simplify_regex b) in 
		if a' = Epsilon then b' else if b' = Epsilon then a' else Or(a', b')
	end
	| Concat(a,b) -> begin
		let (a',b') = (simplify_regex a, simplify_regex b) in 
		if a' = Epsilon then b' else if b' = Epsilon then a' else Concat(a',b')
	end
	| Optional a ->
		let a' = simplify_regex a in 
		if a' = Epsilon then Epsilon else Optional a' 
	| Repeat a->  
		let a' = simplify_regex a in 
		if a' = Epsilon then Epsilon else Repeat a'
	| Epsilon -> Epsilon  

let rec cartesian_product (a : 'a list ) (b : 'b list ) : ('a * 'b) list = 
	match (a,b) with 
		| ([], _) | (_, []) -> []
		| (a::q, l) -> (List.map (fun x -> (a,x)) l)@(cartesian_product q l);;

let conditional_union (a : 'a list ) (b : 'a list ) (cond : bool) : 'a list =
	if cond then a@b else a

let rec local_of_regex : ('a*int) reg -> ('a list * int) local = function  
	| Concat(a,b) -> 
		let (la, pa, sa, fa) = local_of_regex a in 
		let (lb, pb, sb, fb) = local_of_regex b in
		(la && lb, conditional_union pa pb la, conditional_union sb sa lb , fa@fb@(cartesian_product sa pb) ) 
	| Or(a,b) -> 
		let (la, pa, sa, fa) = local_of_regex a in 
		let (lb, pb, sb, fb) = local_of_regex b in
		(la || lb, pa@pb, sb@sa, fa@fb )
	| Optional a -> 
		let (la, pa, sa, fa) = local_of_regex a in 
		(true, pa, sa, fa )
	| Repeat a -> 
		let (la, pa, sa, fa) = local_of_regex a in 
		(la, pa, sa, fa@(cartesian_product sa pa) )
	| Letter (l,n) -> 
		(false, [[l],n] , [[l],n] , [])
	| Joker (cs,n) -> 
		(false, [cs,n] , [cs,n] , [])
	| Epsilon -> (false, [], [], [])

let local_language_of_local ((l, p, s, f) : 'a local ) : 'a local_language =
	 {l = l; p = p; s = s; f = f;} 

let automaton_without_numerotation (auto : ( ('a*int) option, 'a*int )  automaton) : (int,'a) automaton  = 
	let get_id : ('a*int) option -> int = function
		| None -> -1
		| Some (_,n) -> (assert (n >= 0); n)
	in 
		{ init_states = List.map get_id auto.init_states; 
	end_states = List.map get_id auto.end_states; 
	transitions = List.map (fun (s1,(c,_),s2) -> (get_id s1, c, get_id s2)) auto.transitions}

let rec remove_doublons (l : 'a list) : 'a list =
	match l with
		| [] -> []
		| a::q -> if List.mem a q then remove_doublons q else a::(remove_doublons q)

let remove_unnesserary_transitions l =
	let l' = remove_doublons l in
	let already_all_taken_transitions = List.fold_left (fun la (n,c,m) -> if c = None then (n,m)::la else la) [] l' in
	let rec aux l2 =
		match l2 with
			| [] -> []
			| (n,a,m)::q -> if a = None then (n,a,m)::(aux q) 
							else if List.mem (n,m) already_all_taken_transitions then aux q
							else (n,a,m)::(aux q)
	in aux l'

let automaton_without_jokers (auto : (int,'a list) automaton) : (int , 'a) automaton =
	{ 
	init_states = auto.init_states;
	end_states = auto.end_states; 
	transitions = remove_doublons (
			List.flatten (
				List.map 
					(fun (n,a,m) -> List.map ( fun c -> (n,c,m) ) a )
					auto.transitions
			)
		)
	}

let automaton_of_regex_text txt =
	automaton_without_jokers (
		automaton_without_numerotation (
			automaton_of_local_language (
				local_language_of_local (
					local_of_regex (
						simplify_regex(
							regex_of_text (
									linearise (
										char_list_of_string txt
									)
								)
						)
					)
				)
			)
		)
	)

let possible_transitions (auto : ('a, char) automaton) (s : 'a list) : (('a list * char) * 'a list) list =
	let t = Array.make 256 [] in
	List.iter (
				fun (q1, a, q2) ->
					if List.mem q1 s then
						t.(Char.code a) <- q2::t.(Char.code a)
					else
						()
				) auto.transitions ;
	let rec concat n =
	 if n >= 256 then []
		else if t.(n) = [] then concat (n+1)
		else ((s, Char.chr n), List.sort compare t.(n))::(concat (n+1))
	in concat 0

let determinised_transitions (auto : ('a, char) automaton) = 
	let rec aux (states : 'a list list ) transitions newincluded =
		match newincluded with 
			| [] -> (states, transitions)
			| s::q -> if List.mem s states then aux states transitions q else 
				let trs = possible_transitions auto s in
				let nstates = s::states in  
				aux nstates (trs@transitions) ((List.filter (fun x -> not (List.mem x nstates)) (List.map (fun (_,s') -> s') trs))@q)
	in aux [] [] [List.sort compare auto.init_states]

let put_in_htbl ( tab : ('a*'b) list) : ('a , 'b) Hashtbl.t =
	let ht = Hashtbl.create (List.length tab) in
	let rec aux = function 
		| [] -> ()
		| (k,v)::q -> ( Hashtbl.add ht k v ; aux q)
	in aux tab;
	ht;;

let rec do_intersect (l1 : 'a list) (l2 : 'a list) : 'a option =
	match l1 with 
		| [] -> None
		| a::q -> if List.mem a l2 then Some a else do_intersect q l2

let map_in_tbl (l : 'a list) (f : 'a -> 'b) : ('a, 'b) Hashtbl.t =
	let ht = Hashtbl.create (List.length l) in 
	let rec aux = function
		| [] -> ()
		| a::q -> (Hashtbl.add ht a (f a) ; aux q)
	in aux l;
	ht

let determinised_automaton (auto: ('a, char) automaton) : 'a language_determinised_automaton =
	let (states, new_transitions) = determinised_transitions auto in
	let ending_info = map_in_tbl states (do_intersect auto.end_states) in 
	{init_state = List.sort compare auto.init_states; ending_info = ending_info; delta_htbl = put_in_htbl new_transitions}

let compile_regex (re_text : string) : regex_det_auto =
	determinised_automaton (automaton_of_regex_text re_text)

let run_automaton_on (auto : 'a language_determinised_automaton) (word : string) : 'a list =
	let listed_word = char_list_of_string word in 
	let rec run_from s w =
		match w with 
			| [] -> s
			| l::w' -> run_from (Hashtbl.find auto.delta_htbl (s,l)) w'
	in run_from auto.init_state listed_word;;

let accessible_end_state (auto :('a, 'c) language_determinist_automaton) (word:string): 'c option =
	let final_state = run_automaton_on auto word in
	Hashtbl.find auto.ending_info final_state


let recognized (auto :('a, 'c) language_determinist_automaton) (word:string): bool =
	accessible_end_state auto word <> None

let recognizer (reg : string) : string -> bool =
	recognized (compile_regex reg)
