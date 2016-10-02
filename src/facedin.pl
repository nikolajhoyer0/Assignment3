/*******************************************************************************
Copenhagen University, DIKU
Advanced Programming 2016
Assignment 3 - Analysing FacedIn
Nikolaj Høyer  (ctl533@alumni.ku.dk)
Andrew Parli   (qcm239@alumni.ku.dk)

A FacedIn friend graph, G, consists of a set of people, where for each person,
there is a set of other people this person considers to be friends.
The friend graph G is represented as a list of Prolog terms, each of the form
person(X, [X_1, ..., X_n]), where X is an atom representing a person,
and X_1,..., X_n (where n >= 0) is that person’s friend list,
in no particular order, without duplicates, and not including X itself.
The list contains only one person by any given name X.

For example, consider the following friend graph, where each node represents
a person on FacedIn, and a directed edge from X to Y denotes that Y is on X’s
friend list (see assignment). Such a graph can be represented with the
Prolog term.

g0([person(ralf, [susan, ken]),
    person(ken, [ralf]),
    person(susan, [reed, jessica, jen, ralf]),
    person(reed, [tony, jessica]),
    person(jessica, [jen]),
    person(tony, []),
    person(jen, [susan, jessica, tony])]).

BUDDIES : We say that X and Y are buddies if they are on each others’ friends
lists. For example, in g0, Susan and Jen are buddies.

CLIQUES : A clique is a set of at least two people, who are all buddies.
For example, Jessica and Jen form a clique in g0, as do Jen and Susan; but all
three women do not form a clique, because Jessica does not (according to g0)
consider Susan to be her friend.

ADMIRERS : A FacedIn admirer is a person X, who (transitively) likes everyone
else in the network. That is, there is a chain of friendship links from X to
every other person in the graph. For example, Susan is an admirer in g0.

IDOLS : A FacedIn idol is a person X, who is (transitively) liked by everyone
else in the network. That is, there is a chain of friendship links from every
other person in the graph to X. For example, Tony Stark is an idol in g0.

PATHS : A path from X to Y is an alternating list [X1, A1, X2, A2, …, Xn]
(n ≥ 1), where each Xi is a person, such that X1 = X, Xn = Y, and no person
occurs more than once in the list; and where each Ai is either -> or <-, such
that there is an arrow -> between Xi and Xi + 1 if Xi + 1 is on Xi’s friend
list, and an arrow <- if Xi is on Xi + 1’s friend list. For example, one of
many paths from Susan to Jen in g0 is,

                    [susan,->,reed,->,tony,<-,jen]


NOTE: The following code assumes that G is a fully instantiated, well-formed
friend graph.
*******************************************************************************/

/*
 * buddies/3
 * True if person X and Y are buddies in the social network G, specifically
 * when both X likes Y and Y like X are true.
 *    G -> social network   (list of compound terms)
 *    X -> person's name    (atom)
 *    Y -> person's name    (atom)
 */
buddies(G, X, Y) :-
  NodeX = person(X, XList),  % unpack data structure
  NodeY = person(Y, YList),
  inGraph(NodeX, G),         % sanity check
  inGraph(NodeY, G),
  isLiked(X, YList),         % Y likes X
  isLiked(Y, XList).         % X likes Y

/*
 * clique/2
 * True when L is a duplicate-free list of names that form a clique in the
 * friend graph G.
 *     G -> social network   (list of compound terms)
 *     L -> names in clique  (list of atoms)
 */
clique(G, L) :- clique_(G, L).

clique_(G, [Name1, Name2]) :- buddies(G, Name1, Name2).
clique_(G, [Name|Others])  :-
  friendsWithAll(G, Name, Others),
  removeNode(Name, G, NewG),
  clique_(NewG, Others).

/*
 * admirer/2
 * True whenever person X is an admirer in the social network G.
 *    G -> social network   (list of compound terms)
 *    X -> person's name    (atom)
 */
admirer(G, Admirer) :-
  removeNode(Admirer, G, NewG),
  isAdmirer(G, Admirer, NewG).

isAdmirer(_, _, []).
isAdmirer(G, Admirer, [person(P,_)|Others]) :-
  hasPath(G, Admirer, P),
  isAdmirer(G, Admirer, Others).

/*
 * idol/2
 * True whenever person X is an idol in the social network G.
 *    G -> social network   (list of compound terms)
 *    X -> person's name    (atom)
 */
idol(G, Idol) :-
  removeNode(Idol, G, NewG),
  isIdol(G, Idol, NewG).

isIdol(_, _, []).
isIdol(G, Idol, [person(P,_)|Others]) :-
  hasPath(G, P, Idol),
  isIdol(G, Idol, Others).

/*
 * Define a predicate ispath(G, X, Y, P) that holds whenever P is a path from
 * X to Y in G.
 */
ispath(G, X, Y, P) :- ispath_(G, X, Y, P).

/* CASE 1 : Simple Edge */
ispath_(G, X, Y, [X, '->', Y]) :- hasEdge(G, X, Y).
ispath_(G, X, Y, [X, '<-', Y]) :- hasEdge(G, Y, X).

/* CASE 2 : First in Path list */
ispath_(G, X, Y, [X,'->',A|Tail]) :-
  hasEdge(G, X, A),
  removeNode(X, G, NewG),
  ispath_(NewG, X, Y, [A|Tail]).
ispath_(G, X, Y, [X,'<-',A|Tail]) :-
  hasEdge(G, A, X),
  removeNode(X, G, NewG),
  ispath_(NewG, X, Y, [A|Tail]).

/* CASE 3 : End of Path list */
ispath_(G, _, Y, [A,'->',Y|[]]) :-
  hasEdge(G, A, Y).
ispath_(G, _, Y, [A,'<-',Y|[]]) :-
  hasEdge(G, Y, A).

/* CASE 4 : Running through each edge of the Path list */
ispath_(G, X, Y, [A,'->',C|Tail]) :-
  hasEdge(G, A, C),
  removeNode(A, G, NewG),
  ispath_(NewG, X, Y, [C|Tail]).
ispath_(G, X, Y, [A,'<-',C|Tail]) :-
  hasEdge(G, C, A),
  removeNode(A, G, NewG),
  ispath_(NewG, X, Y, [C|Tail]).

/*******************************************************************************

HELPER FUNCTIONS

These are self-implemented versions of some of the predicates from Prolog's
standard library. Many of these predicates were given one or more descriptive
wrappers in order to help make the use of the predicate clearer within the
context of the code.

*******************************************************************************/

/* True if a path exists from A to B */
hasPath(G, A, B) :- hasEdge(G, A, B).
hasPath(G, A, B) :-
  hasEdge(G, A, X),
  removeNode(A, G, Gprime),
  hasPath(Gprime, X, B).

/* True if an edge exists in G from X to Y */
hasEdge(G, X, Y) :-
  select_main(person(X, XFriends), G, _),
  isLiked(Y, XFriends).

friendsWithAll(G, Name1, [Name2]) :- buddies(G, Name1, Name2).
friendsWithAll(G, Name1, [Name2|Others]) :-
  buddies(G, Name1, Name2),
  removeNode(Name2, G, NewG),
  friendsWithAll(NewG, Name1, Others).

/*******************************************************************************

STANDARD FUNCTIONS

These are self-implemented versions of some of the predicates from Prolog's
standard library. Many of these predicates were given one or more descriptive
wrappers in order to help make the use of the predicate clearer within the
context of the code.

*******************************************************************************/

/* Descriptive wrappers for standard member function */
isLiked(PersonX, PersonY_FriendList) :-
  member_main(PersonX, PersonY_FriendList).
inGraph(NodeX, Graph) :- member_main(NodeX, Graph).

/*
 * member_main/2 : True when the element E is a member of the list L.
 *                   Elem - element of list   ('a')
 *                   L    - list              (list 'a')
 */
member_main(Elem, L) :- member_helper(Elem, L).

member_helper(X, [X|_]).
member_helper(X, [_|Tail]) :- member_helper(X, Tail).

/* Descriptive wrapper for standard select function */
removeNode(Name, Graph, NewGraph) :-
  select_main(person(Name,_), Graph, NewGraph).

/* select_main/3 : Trun when List1, with element E is the same as List2 */
select_main(E, List1, List2) :- select_helper(E, List1, List2).
select_helper(E, [E|Tail], Rest).
select_helper(E, [Not_E|Tail], [Not_E|Rest]) :-
  select_helper(E,Tail,Rest).

/* Descriptive wrapper for standard last function */
lastInPath([X|Xs], Last) :-
  last_main(Xs, X, Last).

last_main([], Last, Last).
last_main([X|Xs], _, Last) :-
  last_main(Xs, X, Last).

/*******************************************************************************

GRAPHS AND PATHS FOR TESTING

*******************************************************************************/

g0([person(ralf, [susan, ken]),
    person(ken, [ralf]),
    person(susan, [reed, jessica, jen, ralf]),
    person(reed, [tony, jessica]),
    person(jessica, [jen]),
    person(tony, []),
    person(jen, [susan, jessica, tony])]).

g1([person(ralf, [susan, ken]),
    person(ken, [ralf, susan]),
    person(susan, [reed, jessica, jen, ralf, ken]),
    person(reed, [tony, jessica]),
    person(jessica, [jen]),
    person(tony, []),
    person(jen, [susan, jessica, tony])]).

p0([susan,->,reed,->,tony,<-,jen]).
