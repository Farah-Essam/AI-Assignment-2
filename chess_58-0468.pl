% AI Assignment 2
% Team Members:

% Member 1 
% Name:Farah Essam
% ID: 58-0468
% Tutorial: 10 

% Member 2
% Name:Ahmed Wael 
% ID: 58-0297
% Tutorial: 10 

% Member 3
% Name: Basmala Mohammed 
% ID: 58-15037
% Tutorial: 24

:- include('KB1.pl').
:- use_module(library(assoc)).

% Our single fluent, board(Knights,Bishops,Situation), describes a complete
% configuration. Each list contains (X,Y) coordinates. s0 is the initial
% situation; result(Action,PreviousSituation) represents a successor.
% Keeping both piece lists together preserves consistent source choices.
board(Knights,Bishops,s0) :-
    findall((X,Y),knight_at(X,Y),Knights),
    findall((X,Y),bishop_at(X,Y),Bishops).

% SUCCESSOR-STATE AXIOM: the new board holds exactly when a previous board
% holds and a legal action relates it to the new board. The transition below
% defines both the changed positions and the pieces that persist unchanged.
board(NewKnights,NewBishops,result(Action,PreviousSituation)) :-
    board(Knights,Bishops,PreviousSituation),
    legal_transition(Action,Knights,Bishops,NewKnights,NewBishops).

% Check or generate coordinates before arithmetic and negation are used.
inside_board(X,Y) :-
    grid(Width,Height),
    between(1,Width,X),
    between(1,Height,Y).

% Source and destination coordinates must be instantiated integers.
knight_move(X,Y,H,V) :-
    DX is abs(H-X),
    DY is abs(V-Y),
    (DX =:= 2, DY =:= 1 ; DX =:= 1, DY =:= 2).

bishop_move(X,Y,H,V) :-
    DX is abs(H-X),
    DY is abs(V-Y),
    DX > 0,
    DX =:= DY.

% H and V must be ground: neither type may occupy the destination.
empty_cell(H,V,Knights,Bishops) :-
    \+ member((H,V),Knights),
    \+ member((H,V),Bishops).

% The authoritative transition relation shared by the axiom and search.
% select/3 chooses and removes exactly one source. Backtracking explores
% ambiguous sources. Adding the empty destination preserves piece counts.
% Reusing the other list preserves every piece of the other type.
legal_transition(k(H,V),Knights,Bishops,[(H,V)|Remaining],Bishops) :-
    inside_board(H,V),
    empty_cell(H,V,Knights,Bishops),
    select((X,Y),Knights,Remaining),
    knight_move(X,Y,H,V).
legal_transition(b(H,V),Knights,Bishops,Knights,[(H,V)|Remaining]) :-
    inside_board(H,V),
    empty_cell(H,V,Knights,Bishops),
    select((X,Y),Bishops,Remaining),
    bishop_move(X,Y,H,V).
% No intermediate-square check: bishops are allowed to jump.

% Ground situations request validation; an unbound situation requests search.
% Partially instantiated histories are unsupported. This query predicate is
% not another fluent: board/3 alone describes the changing world state.
goal((KX,KY),(BX,BY),Situation) :-
    inside_board(KX,KY),
    inside_board(BX,BY),
    (KX,KY) \= (BX,BY),
    ( ground(Situation) ->
        board(Knights,Bishops,Situation),
        targets_present((KX,KY),(BX,BY),Knights,Bishops)
    ; var(Situation),
      board(Knights,Bishops,s0),
      bishop_color_possible(BX,BY,Bishops),
      sort(Knights,SortedKnights),
      sort(Bishops,SortedBishops),
      empty_assoc(EmptyVisited),
      put_assoc(state(SortedKnights,SortedBishops),EmptyVisited,true,Visited),
      breadth_first([node(SortedKnights,SortedBishops,s0)],[],Visited,
                    (KX,KY),(BX,BY),Situation)
    ).

targets_present(KnightTarget,BishopTarget,Knights,Bishops) :-
    member(KnightTarget,Knights),
    member(BishopTarget,Bishops).

% A bishop cannot change its square color. This is only an early rejection
% check; the finite visited-state search handles other unreachable goals.
bishop_color_possible(BX,BY,Bishops) :-
    member((X,Y),Bishops),
    (BX+BY) mod 2 =:= (X+Y) mod 2,
    !. % Existence is sufficient; avoid repeating search for other bishops.

% Breadth-first search uses a FIFO queue represented by Front and reversed
% Rear lists. Each node stores a complete board and its nested action history.
% Visited is an immutable association tree, passed through recursion.
% Canonical sorted lists identify boards independently of piece-list order.
breadth_first([node(Knights,Bishops,History)|Front],Rear,Visited,KT,BT,S) :-
    ( targets_present(KT,BT,Knights,Bishops) ->
        S = History
    ; findall(node(NK,NB,result(Action,History)),
              (legal_transition(Action,Knights,Bishops,K,B),
               sort(K,NK),sort(B,NB)),Children),
      enqueue_unseen(Children,Rear,Visited,NextRear,NextVisited),
      breadth_first(Front,NextRear,NextVisited,KT,BT,S)
    ).
breadth_first([],Rear,Visited,KT,BT,S) :-
    Rear = [_|_],
    reverse(Rear,Front),
    breadth_first(Front,[],Visited,KT,BT,S).
% With both queue lists empty, search fails: no reachable board meets the goal.

% Mark each board when enqueued, including duplicates within Children.
% There is no fixed depth limit and no use of global mutable state.
enqueue_unseen([],Rear,Visited,Rear,Visited).
enqueue_unseen([node(K,B,H)|Rest],Rear,Visited,FinalRear,FinalVisited) :-
    Key = state(K,B),
    ( get_assoc(Key,Visited,_) ->
        enqueue_unseen(Rest,Rear,Visited,FinalRear,FinalVisited)
    ; put_assoc(Key,Visited,true,NextVisited),
      enqueue_unseen(Rest,[node(K,B,H)|Rear],NextVisited,FinalRear,FinalVisited)
    ).



