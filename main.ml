(*********************************************************************************************)
(************************** General purpose functions ****************************************)
(*********************************************************************************************)

(* Converts the string s into a list of its characters *)
let char_list_of_string s = List.init (String.length s) (String.get s);;

(* Concatenates a list of characters into a string *)
let rec string_of_char_list = function
	| [] -> ""
	| c::q -> (String.make 1 c)^(string_of_char_list q)

(* Create a range of numbers, so the returned list contains the whole numbers between i and j (both included) *)
let rec range (i:int) (j:int) : int list =
	if i <= j then i::(range (i+1) j) else []

(* Returns a list containing the charachters with ascii codes between i and j (both included) *)
let char_range (i:int) (j:int) : char list =
	List.map Char.chr (range i j)

(* Returns list of the charachters wich are between c1 and c2 (both included) in the ascii table *)
let range_char (c1:char)(c2:char) : char list =
	char_range (Char.code c1) (Char.code c2)

(* Like the set difference : returns l1 without the elements that are in l2 *)
let subtract (l1 : 'a list) (l2 : 'a list) : 'a list =
	List.filter (fun x -> not (List.mem x l2)) l1

(* Returns a list of all couples (u,v) such that u is in a and v is in b *)
let rec cartesian_product (a : 'a list ) (b : 'b list ) : ('a * 'b) list = 
	match (a,b) with 
		| ([], _) | (_, []) -> []
		| (a::q, l) -> (List.map (fun x -> (a,x)) l)@(cartesian_product q l);;

(* Returns a list containing the elements of a and if cond is true those of b  *)
let conditional_union (a : 'a list ) (b : 'a list ) (cond : bool) : 'a list =
	if cond then a@b else a

(* Creates a hashtable with the (key, value) bindings in tab *)
let put_in_htbl ( tab : ('a*'b) list) : ('a , 'b) Hashtbl.t =
	let ht = Hashtbl.create (List.length tab) in
	List.iter ( fun (k,v) -> Hashtbl.add ht k v) tab;
	ht

(* Creates a hashtable binding key and (f key) for key in the list l *)
let map_in_tbl (l : 'a list) (f : 'a -> 'b) : ('a, 'b) Hashtbl.t =
	let ht = Hashtbl.create (List.length l) in 
	List.iter (fun x -> Hashtbl.add ht x (f x) ) l;
	ht

(* Finds an element in common between l1 and l2 or returns None if there are none *)
let rec do_intersect_on (l1 : 'a list) (l2 : 'a list) : 'a option =
	match l1 with 
		| [] -> None
		| a::q -> if List.mem a l2 then Some a else do_intersect_on q l2

(* Returns a list containing the elements of l without repetition *)
let rec remove_duplicates (l : 'a list) : 'a list =
	match l with
		| [] -> []
		| a::q -> if List.mem a q then remove_duplicates q else a::(remove_duplicates q)

(*********************************************************************************************)
(********************************** Regex types  *********************************************)
(*********************************************************************************************)

type ('a ,'b) automaton = {
	init_states: 'a list;
	end_states: 'a list;
	transitions: ('a* 'b* 'a) list
}

type ('a ,'b ,'c) determinist_automaton = {
	init_state: 'a ;
	ending_info: ('a, 'c option) Hashtbl.t ;
	delta_htbl: (('a* 'b), 'a) Hashtbl.t
}
(* Cas particuliers utiles : *)
type ('a, 'c) language_determinist_automaton = ('a , char, 'c) determinist_automaton
type 'a language_determinised_automaton = ('a list, 'a) language_determinist_automaton
type regex_det_auto = int language_determinised_automaton

type captures_infos = {
	nb_parentheses : int;
	parentheses : (int*int) list;
	allowed_transitions_within_capture : (int*int*int, bool) Hashtbl.t 
}

type 'a local_language = {
	l: bool;
	p: 'a list;
	s: 'a list;
	f: ('a*'a) list
}

type 'a local = (bool) * ('a list) * ('a list) * ( ('a* 'a) list )

type 'a reg = 
	| Letters of (char list )*int
	| Or of 'a reg * 'a reg 
	| Optional of 'a reg
	| Repeat of 'a reg
	| Concat of 'a reg * 'a reg
	| Epsilon

type 'a cap_reg = ('a reg) * captures_infos
type state = char*int;;

type compiled_capturer = {
	captures_info : captures_infos;
	determinised_auto : regex_det_auto; 
	backwards_delta : ((char*int), int) Hashtbl.t
}
type compiled_recognizer = regex_det_auto


(*********************************************************************************************)
(*************************** Conversion text to regex ****************************************)
(*********************************************************************************************)

let linearise (regex : 'a list ) : ('a*int) list =
	let rec aux (n:int) : 'a list -> ('a*int) list = function
		| [] -> []
		| c::q -> (c, n)::(aux (n+1) q)
	in
	aux 0 regex

let rec transitions_two_factors (f : ('a* 'a) list ) : ('a* 'a* 'a) list = match f with  
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

(* Creates the regex concatenating all the regex of a list in order *)
let rec concat_list : ('a reg) list -> 'a reg  = function
	| [] -> Epsilon
	| a::q -> Concat (a, (concat_list q))

(* Some usefull sets of characters *)
let range_all : char list = char_range 0 255
let dot_all : char list = (subtract range_all ['\r'; '\n'])
let special_chars : char list = ['('; ')'; '|'; '?';'+';'*';'\\';'.']
let char_classes_names : char list = ['s';'d';'w';'S';'D';'W']
let char_classes_values : char list list = [ [' '; '\n'; '\t'; '\r']; (* \s *) 
								range_char '0' '9'; (* \d *)
								'_'::(range_char '0' '9')@(range_char 'a' 'z')@(range_char 'A' 'Z'); (* \w *) 
								subtract range_all [' '; '\n'; '\t'; '\r'] ; (* \S *)
								subtract range_all (range_char '0' '9'); (* \D *)
								subtract range_all ('_'::(range_char '0' '9')@(range_char 'a' 'z')@(range_char 'A' 'Z'))  (* \W *)
								]
let char_classes : (char * (char list)) list = List.combine char_classes_names char_classes_values

(* Returns the set of chars associated with char class named \c *)
let search_char_class (c : char) : char list option =
	List.assoc_opt c char_classes

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
	| Letters (cs,n) -> 
		(false, [cs,n] , [cs,n] , [])
	| Epsilon -> (false, [], [], [])

let rec add_allowed_transitions_within_capture ( re : (char*int) reg ) ( n : int) ( ht : (int*int*int, bool) Hashtbl.t ) =
	let (_, _ , _, transitions ) = local_of_regex re in
	List.iter (fun ((_,s1),(_,s2)) -> Hashtbl.add ht (n, s1, s2) true ) transitions

(* Main conversion function *)
let capture_regex_of_text (t : (char*int) list) : (char*int) cap_reg =
	let nb_parentheses = ref 0 in
	let parentheses = ref [] in
	let allowed_transitions_within_capture = Hashtbl.create 1 in
	let loop id = Optional (Repeat (Letters (dot_all, id))) in 
	(* 
		res : closed and definitive content
		or_content : last priority content (or is the operator with less priority)
		on_going : still open unfinished content accu 
	 *)
	let rec aux res or_content on_going = function
	| ('\\', _)::('$', n)::[] -> aux res (Concat(or_content,on_going)) (Letters (['$'],n)) []
	| ('$', _)::[] -> (concat_list [res; or_content; on_going], [])
	| [] -> (concat_list [res; or_content; on_going; loop (-3)], [])
	| (')', n)::q -> (concat_list [res; or_content; on_going], (')', n)::q)
	| ('(', n)::q -> begin
		match aux res Epsilon Epsilon q with 
		| (reg1, (')', m)::q') -> begin
									parentheses := (n,m)::!parentheses; 
									nb_parentheses := !nb_parentheses + 1;
									add_allowed_transitions_within_capture reg1 n allowed_transitions_within_capture;
									aux res (Concat(or_content,on_going)) reg1 q' 
								end
		| _ -> failwith ("Parentheses at position "^string_of_int n ^ " is not closed ")
	end
	| ('|', _)::q -> let (reg1, q') = aux Epsilon Epsilon Epsilon q in aux res (Or(Concat(or_content,on_going),reg1)) Epsilon q'
	| ('?', _)::q -> aux res or_content (Optional on_going) q
	| ('+', _)::q -> aux res or_content (Repeat on_going) q
	| ('*', _)::q -> aux res or_content (Optional (Repeat on_going)) q
	| ('.', n)::q -> aux res (Concat(or_content,on_going)) (Letters (dot_all , n) ) q
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
								| (None, m)::q -> failwith ("In brackets : the '-' at postion "^(string_of_int m)^" should be associated with two neighours, you can't begin with '-' nor have 'a-b-c'")
								| (Some c,_)::q ->  c::(get_char_set q)
						in 
						let ( l , q') = get_inside_brackets q in 
						let cs = get_char_set l in 
						aux res (Concat(or_content,on_going)) (Letters (cs , n) ) q'
	| ('\\', _)::(ch,n)::q -> 
		if not (List.mem ch special_chars) then
		match search_char_class ch with
			| None -> failwith ("Cannot escape non special character : '"^(String.make 1 ch)^"' at position "^(string_of_int n) )
			| Some cl -> aux res (Concat(or_content,on_going)) (Letters (cl , n) ) q
		else aux res (Concat(or_content,on_going)) (Letters ([ch],n)) q
	| (ch,n)::q -> if ch = '\\' then failwith "Cannot end the string with backslash, backslash has to escape something !"
	else aux res (Concat(or_content,on_going)) (Letters ([ch],n)) q
	in 
	let (t', begin_loop) = 
		match t with
			| ('^', _)::t2 -> (t2, false)
			| ('\\',_)::('^', n)::t2 -> (('^', n)::t2, true)
			| _ -> (t, true)
	in 
	match aux Epsilon Epsilon Epsilon t' with 
		| (_ , (a,n)::_) -> failwith ("unexpected "^(String.make 1 a)^" at postion "^string_of_int n)
		
		| (reg, []) -> (if begin_loop then Concat (loop (-2) ,reg)  else reg ), 
							{
								nb_parentheses = !nb_parentheses;
								parentheses = ( List.sort (fun (n1,m1) (n2,m2) -> n1 - n2) !parentheses);
								allowed_transitions_within_capture = allowed_transitions_within_capture
							} 
	

let rec simplify_regex (reg : 'a reg) : 'a reg =
	match reg with 
	| Letters _ -> reg 
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

let local_language_of_local ((l, p, s, f) : 'a local ) : 'a local_language =
	 {l = l; p = p; s = s; f = f;} 

let automaton_without_numerotation (auto : ( ('a* int) option, 'a* int) automaton ) : (int, 'a) automaton  = 
	let get_id : ('a*int) option -> int = function
		| None -> -1
		| Some (_,n) -> (assert (n <> -1); n)
	in 
		{ init_states = List.map get_id auto.init_states; 
	end_states = List.map get_id auto.end_states; 
	transitions = List.map (fun (s1,(c,_),s2) -> (get_id s1, c, get_id s2)) auto.transitions}

let automaton_flattened_letters (auto : (int,'a list) automaton) : (int , 'a) automaton =
	{ 
	init_states = auto.init_states;
	end_states = auto.end_states; 
	transitions = remove_duplicates (
			List.flatten (
				List.map 
					(fun (n,a,m) -> List.map ( fun c -> (n,c,m) ) a )
					auto.transitions
			)
		)
	}

let capture_automaton_of_regex_text txt =
	let (re,prt_info) = 
	capture_regex_of_text (
		linearise (
			char_list_of_string txt
		)
	) in  
	automaton_flattened_letters (
		automaton_without_numerotation (
			automaton_of_local_language (
				local_language_of_local (
					local_of_regex (
						simplify_regex(
							re
						)
					)
				)
			)
		)
	), prt_info

let automaton_of_regex_text txt = 
	let (auto, _) = capture_automaton_of_regex_text txt in auto

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

let determinised_automaton (auto: ('a, char) automaton) : 'a language_determinised_automaton =
	let (states, new_transitions) = determinised_transitions auto in
	let ending_info = map_in_tbl states (do_intersect_on auto.end_states) in 
	{init_state = List.sort compare auto.init_states; ending_info = ending_info; delta_htbl = put_in_htbl new_transitions}

(*********************************************************************************************)
(**************************** Running regex functions ****************************************)
(*********************************************************************************************)

let run_automaton_on (auto : 'a language_determinised_automaton) (word : string) : 'a list option =
	let listed_word = char_list_of_string word in 
	let rec run_from s_opt w =
		match s_opt with
			| None -> None
			| Some s -> match w with 
						| [] -> Some s
						| l::w' -> run_from (Hashtbl.find_opt auto.delta_htbl (s,l)) w'
	in run_from (Some auto.init_state) listed_word;;

let accessible_end_state (auto :('a, 'c) language_determinist_automaton) (word:string): 'c option =
	match run_automaton_on auto word with
		| None -> None 
		| Some final_state -> Hashtbl.find auto.ending_info final_state

let get_execution_reversed (auto : 'a language_determinised_automaton) (listed_word : char list) : 'a list list =
	let states = ref [] in 
	let rec run_from s_opt w =
		match s_opt with
			| None -> states := []
			| Some s -> states := s::!states;
					match w with 
					| [] -> ()
					| l::w' ->  run_from (Hashtbl.find_opt auto.delta_htbl (s,l)) w'
	in run_from (Some auto.init_state) listed_word;
	!states

let reverse_find_path_of_spath (reversed_super_path : 'a list list) (reversed_word : char list) (back_delta : (char* 'a, 'a) Hashtbl.t) (from : 'a) : 'a list =
	let rec find_from (rev_super_path : 'a list list) (rev_w : char list) (start : 'a) = 
		match rev_super_path, rev_w with
			| [],[] -> [] (* le dernier élément ignoré, c'est toujours l'état initial i.e. -1*)
			| [],_ | _,[] -> failwith "The size of the path should correspond to the size of the word !"
			| sstate::rev_pth', a::rev_w' -> 
			begin
				match do_intersect_on (Hashtbl.find_all back_delta (a, start)) sstate with
						| None -> failwith "Transitions in super path should be allowed by the presence of an antecedant to any element in the next super state."
						| Some s -> start::(find_from rev_pth' rev_w' s)
			end
	in find_from reversed_super_path reversed_word from

let find_accepting_path_reversed (det_auto) (back_delta) (word : char list) (rev_word : char list) =
	match get_execution_reversed det_auto word with
		| [] -> None
		| finish_super_state::reversed_super_path  -> begin
			match (Hashtbl.find det_auto.ending_info finish_super_state) with
				| None -> None
				| Some final_state -> Some (reverse_find_path_of_spath reversed_super_path rev_word back_delta final_state)
		end

let find_captures reversed_word reversed_path cap_info =
	let captures = Array.make cap_info.nb_parentheses [] in
	let ht = cap_info.allowed_transitions_within_capture in 
	let add_to_captures (a : char ) (s : int) (prev_s : int) =
		let rec aux (parentheses : (int*int) list ) (i : int)  = 
			match parentheses with
				| [] -> ()
				| (n,m)::ps' ->
				(match Hashtbl.find_opt ht (n, s, prev_s) with
						| None -> if n <= s && s <= m then captures.(i) <- (String.make 1 a)::captures.(i)
						| Some true -> (match captures.(i) with
											| accu::q -> captures.(i) <- ((String.make 1 a)^accu)::q
											| [] -> failwith "pas possible") 
						| _ -> failwith "pas possible"); aux ps' (i+1)
		in aux cap_info.parentheses 0
	in
	let rec update_captures_from rev_w rev_pth prev_s =
		match rev_w, rev_pth with
			| [], [] -> ()
			| [], _ | _, [] -> failwith "The word and the path should have same length. Did you forget to remove the initial state ?"
			| a::rev_w', s::rev_pth' -> (add_to_captures a s prev_s; update_captures_from rev_w' rev_pth' s)
	in update_captures_from reversed_word reversed_path (-1) ;
	captures

(*********************************************************************************************)
(********************************* Public interface ******************************************)
(*********************************************************************************************)

let compile_capture_regex re_text =
	let (auto, ps_info) = capture_automaton_of_regex_text re_text in 
	let det_auto = determinised_automaton auto in
	let back_delta = Hashtbl.create (List.length auto.transitions) in
	let rec init_back_delta tr =
		match tr with
			| [] -> ()
			| (q,a,q')::tr' -> (Hashtbl.add back_delta (a,q') q ;init_back_delta tr')
	in init_back_delta auto.transitions;
	{
		captures_info = ps_info;
		determinised_auto = det_auto; 
		backwards_delta = back_delta
	}

let compile_regex (re_text : string) : regex_det_auto =
	determinised_automaton (automaton_of_regex_text re_text)

let captured cap_re word = 
	let listed_word = char_list_of_string word in
	let reversed_word = List.rev listed_word in
	match find_accepting_path_reversed cap_re.determinised_auto cap_re.backwards_delta listed_word reversed_word with
		| None -> None
		| Some rev_path -> Some (find_captures reversed_word rev_path cap_re.captures_info)

let recognizer_of_capturer cap_re =
	cap_re.determinised_auto

let recognized (auto :('a, 'c) language_determinist_automaton) (word:string): bool =
	accessible_end_state auto word <> None

let recognizer (reg : string) : string -> bool =
	recognized (compile_regex reg)

let capturer (reg : string) : string -> string list array option =
	captured (compile_capture_regex reg)