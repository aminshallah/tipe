(*Ici on va tester sans les transports*)

type transport =
  | Pied
  | Voiture
  | Velo
  | Aucun

type automate = {
  mutable etats : int;
  mutable transitions : (int * transport * int) list;
  mutable init : int list;
  mutable finaux : int list;
}

type 'a priopqueue = (int * 'a) list ref

type sommet = int

type graph_dij = {
  taille : int;
  (* les sommets sont des entiers entre 0 et taille-1 *)
  adj : (int * transport * sommet) list array;
  entree : sommet;
}

type graphe = (int * transport * sommet) list array

let ajouter_etats (m : automate) (final : bool) =
  if final then m.finaux <- m.etats :: m.finaux;
  m.etats = m.etats + 1

let delta (m : automate) (p : int) (etiquette : transport) : int list =
  let rec aux (p : int) (liste : (int * transport * int) list) =
    match liste with
    | [] -> []
    | (x, a, q) :: xs when x = p && a = etiquette -> q :: aux p xs
    | x :: xs -> aux p xs
  in
  aux p m.transitions

let suivant (m : automate) (p : int) =
  let rec aux (p : int) (liste : (int * transport * int) list) =
    match liste with
    | [] -> []
    | (x, a, q) :: xs when x = p -> q :: aux p xs
    | x :: xs -> aux p xs
  in
  aux p m.transitions

let ajouter_transition (m : automate) (p : int) (a : transport) (q : int) =
  m.transitions <- (p, a, q) :: m.transitions

let voisins (g : graphe) (s : int) = g.(s)

let degre_sommet (g : graphe) (s : int) =
  let ent = List.length g.(s) in
  let deg = ref ent in
  let n = Array.length g in
  let rec aux (lst : (int * transport * sommet) list) (k : int) : int =
    match lst with
    | [] -> 0
    | (x, a, q) :: xs when q = k -> 1 + aux xs k
    | x :: xs -> aux xs k
  in
  for i = 0 to n - 1 do
    if i <> s then
      let tmp = aux g.(i) s in
      deg := !deg + tmp
  done;
  !deg

let graphe_retourne (g : graphe) : graphe =
  let n = Array.length g in
  let retourne = Array.make n [] in
  let aux (t1 : 'a array) (t2 : 'a array) (k : int) =
    match t1.(k) with
    | [] -> ()
    | (x, a, s) :: xs -> t2.(s) <- (x, a, k) :: t2.(s)
  in
  for i = 0 to n - 1 do
    aux g retourne i
  done;
  retourne

let vide () : 'a priopqueue = ref []

let inserer (x : 'a) (clef : int) (q : 'a priopqueue) : unit =
  if List.exists (fun (_, v) -> x = v) !q then
    failwith "l'element est déjà dans la file"
  else q := (clef, x) :: !q

let est_vide (q : 'a priopqueue) : bool = !q = []

let rec trouve_min_aux (min_val : 'a) (min_clef : int) (q : (int * 'a) list) :
    int * 'a =
  match q with
  | [] -> (min_clef, min_val)
  | (clef, _) :: q when clef > min_clef -> trouve_min_aux min_val min_clef q
  | (clef, v) :: q -> trouve_min_aux v clef q

let trouve_min (q : (int * 'a) list) : 'a =
  match q with
  | [] -> failwith "trouve_min: la file est vide"
  | (clef, v) :: q -> snd (trouve_min_aux v clef q)

let rec supprime (x : 'a) (q : (int * 'a) list) : (int * 'a) list =
  match q with
  | [] -> []
  | (_, v) :: q when v = x -> q
  | (clef, v) :: q -> (clef, v) :: supprime x q

let extraire_min (q : 'a priopqueue) : 'a =
  if !q = [] then failwith "extraire_min: file vide"
  else
    let min = trouve_min !q in
    q := supprime min !q;
    min

let diminuer_clef (x : 'a) (clef : int) (q : 'a priopqueue) : unit =
  let rec diminuer_aux (l : (int * 'a) list) : (int * 'a) list =
    match l with
    | [] -> failwith "diminuer_clef : l'élément n'est pas présent"
    | (_, v) :: q when v = x -> (clef, x) :: q
    | (c, v) :: q -> (c, v) :: diminuer_aux q
  in
  q := diminuer_aux !q

let dijkstra g =
  let q = vide () in
  let dist =
    Array.init g.taille (fun i -> if i = g.entree then 0 else max_int)
  in
  let pere = Array.init g.taille (fun i -> i) in
  for i = 0 to g.taille - 1 do
    (* initialisation de la file *)
    inserer (i : sommet) (dist.(i) : int) q
  done;
  while not (est_vide q) do
    let x = extraire_min q in
    (* on regarde les adjacents de x *)
    List.iter
      (fun (c, t, y) ->
        if dist.(y) > dist.(x) + c then begin
          pere.(y) <- x;
          dist.(y) <- dist.(x) + c;
          diminuer_clef y dist.(y) q
        end)
      g.adj.(x)
  done;
  (dist, pere)

let dijkstra2 g =
  let q = vide () in
  let dist =
    Array.init g.taille (fun i -> if i = g.entree then 0 else max_int)
  in
  let pere = Array.init g.taille (fun i -> i) in

  (* initialisation de la file *)
  inserer (g.entree : sommet) 0 q;
  while not (est_vide q) do
    let x = extraire_min q in
    (* on regarde les adjacents de x *)
    List.iter
      (fun (c, t, y) ->
        if dist.(y) > dist.(x) + c then begin
          if dist.(y) = max_int then inserer y (dist.(x) + c) q
          else diminuer_clef y dist.(y) q;
          pere.(y) <- x;
          dist.(y) <- dist.(x) + c
        end)
      g.adj.(x)
  done;
  (dist, pere)

let dijkstra3 (g : graphe) entree =
  let q = vide () in
  let taille = Array.length g in
  let dist = Array.init taille (fun i -> if i = entree then 0 else max_int) in
  let visite =
    Array.init taille (fun i -> if i = entree then true else false)
  in

  (* initialisation de la file *)
  inserer (entree : sommet) 0 q;
  while not (est_vide q) do
    let x = extraire_min q in
    (* on regarde les adjacents de x *)
    List.iter
      (fun (c, t, y) ->
        if dist.(y) > dist.(x) + c then begin
          if dist.(y) = max_int then inserer y (dist.(x) + c) q
          else diminuer_clef y dist.(y) q;
          visite.(y) <- true;
          dist.(y) <- dist.(x) + c
        end)
      g.(x)
  done;
  (dist, visite)

let extraire (a : int option) : int =
  match a with
  | None -> max_int
  | Some x -> x

let union l1 a = if List.mem a l1 then l1 else a :: l1

let dijkstra4 (g : graphe) entree =
  let q = vide () in
  let taille = Array.length g in
  let dist = Array.init taille (fun i -> if i = entree then Some 0 else None) in
  let visite = ref [ entree ] in

  (* initialisation de la file *)
  inserer (entree : sommet) 0 q;
  while not (est_vide q) do
    let x = extraire_min q in
    (* on regarde les adjacents de x *)
    List.iter
      (fun (c, t, y) ->
        if extraire dist.(y) > extraire dist.(x) + c then begin
          if dist.(y) = None then inserer y (extraire dist.(x) + c) q
          else diminuer_clef y (extraire dist.(y)) q;
          visite := union !visite y;
          dist.(y) <- Some (extraire dist.(x) + c)
        end)
      g.(x)
  done;
  (dist, !visite)

(*algorithme 1 et 2*)
let point_rencontre g dp dc =
  (*ici l'objectif est de déterminer tous les sommets attteignables depuis les deux origines, ils déterminent alors des points de rencontre potentiels. On ne cherche pas à s'occuper desquels sont les plus proches pour l'instant.
    Pour ce faire : on récupère les sommets atteignables depuis les deux sommets et on teste*)
  let dist_p, visite_p = dijkstra4 g dp in
  let dist_c, visite_c = dijkstra4 g dc in
  let rec aux l1 l2 res =
    match l1 with
    | [] -> res
    | x :: xs -> if List.mem x l2 then aux xs l2 (x :: res) else aux xs l2 res
  in
  (aux visite_p visite_c [], dist_p, dist_c)

(*algo 4*)

let point_separation g ac =
  (*ici on cherche à déterminer le lieu de dépose, il est déterminé selon l'arrivée du conducteur, de sorte à ce qu'il dépose le piéton sur son chemin.
     Pour ce faire on cherche tous les points qui atteignent ce point d'arrivee. On applique dijsktra sur le grpahe retourné depuis l'origine*)
  let retourne = graphe_retourne g in
  dijkstra4 retourne ac


let rec separation_communs l1 l2 res = 
  match l1 with
    | [] -> res
    | x :: xs -> if List.mem x l2 then separation_communs xs l2 res else separation_communs xs l2 (x :: res)

(*algo 5*)
let meilleure_separation g ac ap =
  let separation_potentielle = snd (point_separation g ac) in
  let retourne = graphe_retourne g in
  let dist_p, visite_p = dijkstra4 retourne ap in
  let communs = ref [] in
  let rec aux l1 l2 res =
    match l1 with
    | [] -> res
    | x :: xs -> if List.mem x l2 then aux xs l2 (x::res) else aux xs l2 res
  in
  communs := aux visite_p separation_potentielle [];
  let rec aux2 lst min meilleure_sep =
    match lst with
    | [] -> meilleure_sep +1
    | x :: xs -> if dist_p.(x) <> None && extraire dist_p.(x) < min then 
        aux2 xs (extraire dist_p.(x)) x else aux2 xs min meilleure_sep
    
  in
  aux2 !communs max_int 198797

(*algo 3*)

let meilleur_point_rencontre g dc dp ac ap =
  let rencontres_potentielles, couts_p, couts_c = point_rencontre g dp dc in
  let n = Array.length g in
  let xoff = meilleure_separation g ac ap in
  let retourne = graphe_retourne g in
  let dist, visite = dijkstra4 retourne xoff in
  let poids = Array.make n None in
  for i = 0 to n - 1 do
    if couts_p.(i) <> None && couts_c.(i) <> None && dist.(i) <> None then
      poids.(i) <-
        Some (extraire couts_p.(i) + extraire couts_c.(i) + extraire dist.(i))
  done;
  let min = ref max_int in
  let meilleure_rencontre = ref 0 in
  let rec aux lst =
    match lst with
    | [] -> ()
    | x :: xs when poids.(x) <> None && extraire poids.(x) < !min ->
        min := extraire poids.(x);
        meilleure_rencontre := x;
        aux xs
    | x :: xs -> aux xs
  in
  aux rencontres_potentielles;
  (!meilleure_rencontre, xoff)

let a = 0

and b = 1

and c = 2

and d = 3

and e = 4

and f = 5

and g = 6

and h = 7

let (g1 : graphe) =
  [|
    [ (5, Velo, b); (6, Velo, e); (1, Velo, f) ];
    (*a*)
    [ (9, Velo, g) ];
    (*b*)
    [ (4, Velo, d); (8, Velo, g) ];
    (*c*)
    [ (5, Velo, h) ];
    (*d*)
    [ (4, Velo, f) ];
    (*e*)
    [ (8, Velo, b); (3, Velo, g) ];
    (*f*)
    [ (2, Velo, d) ];
    (*g*)
    [ (4, Velo, g) ] (*h*);
  |]


let amin = "lpb"