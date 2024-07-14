let char_list_of_string s = List.init (String.length s) (String.get s);;
let rec string_of_char_list = function
	| [] -> ""
	| c::q -> (String.make 1 c)^(string_of_char_list q)
;;

let rec range (i:int) (j:int) : int list =
	if i < j then i::(range (i+1) j) else []

let char_range (c1:char)(c2:char) : char list =
	List.map Char.chr (range (Char.code c1) (Char.code c2))
(* 
let point_chars = List.filter ( fun x -> not (List.mem x ['\n'; '\r'] ) ) (char_range (Char.chr 0) (Char.chr 255));;

let rec replace_points_aux in_brackets = function
	| [] -> []
	| '\\'::'.'::q  -> '.'::(replace_points in_brackets q)
	| '\\'::'['::q  -> '\\'::'['::(replace_points in_brackets q)
	| '['::q -> '['::(replace_points true q)
	| '\\'::']'::q -> '\\'::']'::(replace_points in_brackets q)
	| ']'::q -> ']'::(replace_points false q)
	| '.'::q -> if in_brackets then point_chars@(replace_points in_brackets q) else 
		('['::point_chars@[']'])@(replace_points in_brackets q)
	| c::q -> c::(replace_points in_brackets q)

let replace_points s = replace_points_aux false s;;
 *)
let hook regex =
	let rec aux = function
		| [] -> failwith "not ended ["
		| '['::q -> failwith "Cannot open '[' two times, did you forget to escape it or to close the previous one ?"
		| '\\'::c::q when List.mem c [']';'-'] -> let s, q' = aux q in c::'|'::s, q'
		| c1::'-'::c2::q when not (List.mem c2 [']';'-']) -> aux ((char_range c1 c2)@q)
		| c::']'::q -> [c; ')'], q
		| c::q -> let s, q' = aux q in c::'|'::s, q'
	in
	let rec aux' = function
		| [] -> []
		| '\\'::'['::q -> '['::(aux' q)
		| '['::q ->
			let s, q = aux q in
			'('::(s@(aux' q))
		| c::q -> c::(aux' q)
	in
	aux' regex
;;

type ('a ,'b) automaton = {
	init_states: 'a list;
	end_states: 'a list;
	transitions: ('a*'b*'a) list
};;

type ('a ,'b) determinised_automaton = {
	init_state: 'a ;
	ending_info: ('a,bool) Hashtbl.t ;
	delta_htbl: (('a*'b), 'a) Hashtbl.t
};;

type 'a local_language = {
	l: bool;
	p: 'a list;
	s: 'a list;
	f: ('a*'a) list
}

type 'a reg = 
	| Letter of 'a
	| CharactersCode of 'a list
	| Or of 'a reg * 'a reg 
	| Optional of 'a reg
	| Repeat of 'a reg
	| Concat of 'a reg * 'a reg
	| Epsilon

type state = char*int;;

let linearise regex =
	let rec aux n = function
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

let rec concat_list = function
	| [] -> Epsilon
	| a::q -> Concat (a, (concat_list q))
let special_chars = ['('; ')'; '|'; '?';'+';'*';'\\'];;

let rec cut_at_not_escaped_square_bracket l = 
	match l with 
	 | [] -> failwith "']' missing !"
	 | ('\\', n)::a::l' -> let (c, q) = cut_at_not_escaped_square_bracket l' in
	 	( ('\\', n)::a::c, q )
	 | (']', _)::l' -> ([], l')
	 | ('[', n)::l' -> (failwith "Second '[' opened at position "^(string_of_int n)^" maybe you forgot to escape it ?" )
	 | a::l' -> let (c, q) = cut_at_not_escaped_square_bracket l' in
	 	( a::c, q )

let regex_of_text (t : (char*int) list) : (char*int) reg  = 
	let rec aux res or_content on_going = function
	| (')', n)::q -> (concat_list [res; or_content; on_going], (')', n)::q)
	| ('(', n)::q -> begin 
		match aux res Epsilon Epsilon q with 
		| (reg1, (')', _)::q') -> aux res (Concat(or_content,on_going)) reg1 q'
		| _ -> failwith ("Parentheses at position "^string_of_int n ^ " is not closed ")
	end
	| ('[', n)::q -> let (c,q') = cut_at_not_escaped_square_bracket q in aux res (Concat(or_content,on_going)) (CharactersCode c) q'
	| ('|', _)::q -> let (reg1, q') = aux Epsilon Epsilon Epsilon q in aux res (Or(Concat(or_content,on_going),reg1)) Epsilon q'
	| ('?', _)::q -> aux res or_content (Optional on_going) q
	| ('+', _)::q -> aux res or_content (Repeat on_going) q
	| ('*', _)::q -> aux res or_content (Optional (Repeat on_going)) q
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
		| (_ , (a,n)::_) -> failwith ("unexpected '"^(String.make 1 a)^"' at postion "^string_of_int n)
	 

let rec simplify_regex reg =
	match reg with 
	| Letter a -> reg 
	| CharactersCode c -> reg 
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

let rec cartesian_product a b = 
	match (a,b) with 
		| ([], _) | (_, []) -> []
		| (a::q, l) -> (List.map (fun x -> (a,x)) l)@(cartesian_product q l);;

let conditional_union a b cond =
	if cond then a@b else a

let rec local_of_regex = function  
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
	| Letter a -> 
		(false, [a] , [a] , [])
	| Epsilon -> (false, [], [], [])

let local_language_of_local (l, p, s, f) = {l = l; p = p; s = s; f = f;} 

let automaton_without_numerotation auto = 
	let get_id = function
		| None -> -1
		| Some (_,n) -> (assert (n >= 0); n)
	in 
		{ init_states = List.map get_id auto.init_states; 
	end_states = List.map get_id auto.end_states; 
	transitions = List.map (fun (s1,(c,_),s2) -> (get_id s1, c, get_id s2)) auto.transitions}

let automaton_of_regex_text txt = 
	automaton_without_numerotation (
		automaton_of_local_language (
			local_language_of_local (
				local_of_regex (
					simplify_regex(
						regex_of_text (
							linearise (
								hook (
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
;;

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

let rec do_intersect (l1 : 'a list) (l2 : 'a list) : bool =
	match l1 with 
		| [] -> false
		| a::q -> (List.mem a l2) || (do_intersect q l2)

let map_in_tbl (l : 'a list) (f : 'a -> 'b) : ('a, 'b) Hashtbl.t =
	let ht = Hashtbl.create (List.length l) in 
	let rec aux = function
		| [] -> ()
		| a::q -> (Hashtbl.add ht a (f a) ; aux q)
	in aux l;
	ht

let determinist_automaton (auto: ('a, char) automaton) : ('a list, char) determinised_automaton =
	let (states, new_transitions) = determinised_transitions auto in
	let ending_info = map_in_tbl states (do_intersect auto.end_states)in 
	{init_state = List.sort compare auto.init_states; ending_info = ending_info; delta_htbl = put_in_htbl new_transitions}

let compile_regex (re : string) : (int list, char) determinised_automaton =
	determinist_automaton (automaton_of_regex_text re);;

let run_automaton_on (auto :('a, char) determinised_automaton) (word : string) : 'a option =
	let listed_word = char_list_of_string word in 
	let rec run_from s_opt w =
		match s_opt with 
			| None -> None
			| Some s -> 
			match w with 
				| [] -> Some s
				| l::w' -> run_from (Hashtbl.find_opt auto.delta_htbl (s,l) ) w'
	in run_from (Some auto.init_state) listed_word;;

let recognized (auto :('a, char) determinised_automaton) (word:string): bool =
	match run_automaton_on auto word with
		| None -> false
		| Some finish_state -> Hashtbl.find auto.ending_info finish_state

let recognizer (reg : string) : string -> bool =
	recognized (compile_regex reg)
;;