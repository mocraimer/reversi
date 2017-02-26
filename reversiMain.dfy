	datatype Disk = White | Black
type Board = map<Position,Disk>
type Position = (int,int)
datatype Direction = Up | UpRight | Right | DownRight | Down | DownLeft | Left | UpLeft 

method Main()
{/*
	var board: Board := InitBoard();
	var player: Disk := Black;
	var legalMoves := FindAllLegalMoves(board, player);
	assert |legalMoves| > 0 by
	{
		// evidence that there are legal moves to begin with
		assert InitState(board);
		LemmaInitBlackHasLegalMoves(board);
		assert LegalMove(board, Black, (3,2));
		assert (3,2) in AllLegalMoves(board, Black);
	}
	while |legalMoves| != 0
		invariant ValidBoard(board) && (player == Black || player == White)
		invariant legalMoves == AllLegalMoves(board, player)
		invariant |legalMoves| == 0 <==> AllLegalMoves(board, Black) == AllLegalMoves(board, White) == {}
		decreases AvailablePositions(board)
	{
		var move;
		if player == Black
		{
			assert ValidBoard(board) && legalMoves <= AllLegalMoves(board, Black);
			assert forall pos :: pos in legalMoves <==> LegalMove(board,Black,pos);
			assert legalMoves != {};
			move := SelectBlackMove(board, legalMoves);
		}
		else
		{
			assert ValidBoard(board) && legalMoves <= AllLegalMoves(board, White);
			assert forall pos :: pos in legalMoves <==> LegalMove(board,White,pos);
			assert legalMoves != {};
			move := SelectWhiteMove(board, legalMoves);
		}
		PrintMoveDetails(board, player, move);
		board := PerformMove(board, player, move);
		player := if player == Black then White else Black;
		legalMoves := FindAllLegalMoves(board, player);
		if |legalMoves| == 0
		{
			// the current player has no legal move to make so the turn goes back to the opponent
			player := if player == White then Black else White;
			legalMoves := FindAllLegalMoves(board, player);
		}
	}
	assert AllLegalMoves(board, Black) == AllLegalMoves(board, White) == {};
	var blacks, whites := TotalScore(board);
	PrintResults(blacks, whites);
*/}

method PrintMoveDetails(board: Board, player: Disk, move: Position)
	requires ValidBoard(board) && LegalMove(board, player, move)
{
	print "\n", player, " is placed on row ", move.0, " and column ", move.1;
	var reversibleDirections := FindAllLegalDirectionsFrom(board, player, move);
	print " with reversible directions ", reversibleDirections;
	var reversiblePositions := FindAllReversiblePositionsFrom(board, player, move);
	print " and reversible positions ", reversiblePositions;
}

method PrintResults(blacks: nat, whites: nat)
{
	print "\nGame Over.\nAnd the winner is... ";
	print if blacks > whites then "The Black." else if blacks < whites then "The White." else "it's a tie.";
	print "\nFinal Score: ", blacks, " Black disks versus ", whites, " White disks.";
}

predicate ValidBoard(b: Board)
{
	forall pos :: pos in b ==> ValidPosition(pos)
}

function method ValidPositions(): set<Position>
{
	{
		(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),
		(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),
		(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),
		(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),
		(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),
		(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),
		(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),
		(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7)
	}
}

predicate ValidPosition(pos: Position)
{
	pos in ValidPositions()
}

predicate AvailablePosition(b: Board, pos: Position)
	requires ValidBoard(b)
{
	ValidPosition(pos) && pos !in b
}

predicate OccupiedPosition(b: Board, pos: Position)
	requires ValidBoard(b)
{
	ValidPosition(pos) && pos in b
}

predicate OccupiedBy(b: Board, pos: Position, player: Disk)
	requires ValidBoard(b)
{
	OccupiedPosition(b, pos) && b[pos] == player
}

function AvailablePositions(b: Board): set<Position>
	requires ValidBoard(b)
{
	set pos | pos in ValidPositions() && AvailablePosition(b, pos)
}

function PlayerPositions(b: Board, player: Disk): set<Position>
	requires ValidBoard(b)
{
	set pos | pos in ValidPositions() && OccupiedBy(b, pos, player)
}

function Count(b: Board, player: Disk): nat
	requires ValidBoard(b)
{
	|PlayerPositions(b, player)|
}
predicate LegalMove(b: Board, player: Disk, pos: Position)
	requires ValidBoard(b)
{
	AvailablePosition(b, pos)	&&
	exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction)
}

function Opponent(player: Disk): Disk
{
	if player == White then Black else White
}

function AllLegalMoves(b: Board, player: Disk): set<Position>
	requires ValidBoard(b)
{
	set move: Position | move in AvailablePositions(b) && LegalMove(b, player, move)
}

function ReversiblePositionsFrom(b: Board, player: Disk, move: Position): set<Position>
	requires ValidBoard(b)
{
	var reversibleDirections: set<Direction> := ReversibleDirections(b, player, move);
	set pos | pos in ValidPositions() && exists d :: d in reversibleDirections && pos in ReversibleVectorPositions(b, player, move, d)
}

function ReversibleDirections(b: Board, player: Disk, move: Position): set<Direction>
	requires ValidBoard(b)
	ensures var result := ReversibleDirections(b, player, move); forall dir :: dir in result ==> ReversibleVectorFrom(b, player, move, dir)
{
	if !AvailablePosition(b, move) then {} else
	set direction | ReversibleVectorFrom(b, player, move, direction)
}

predicate ReversibleVectorFrom(b: Board, player: Disk, move: Position, direction: Direction)
	requires ValidBoard(b) && ValidPosition(move)
{
	var vector := VectorPositionsFrom(move, direction);
	ReversibleVector(b, vector, player)
}

predicate ReversibleVector(b: Board, vector: seq<Position>, player: Disk)
	requires ValidBoard(b)
	requires forall pos :: pos in vector ==> ValidPosition(pos)
{
	|vector| >= 3 && AvailablePosition(b, vector[0]) &&
	exists j: nat :: 1 < j < |vector| && OccupiedBy(b, vector[j], player) && 
		forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], Opponent(player))
}

function ReversibleVectorPositions(b: Board, player: Disk, move: Position, direction: Direction): set<Position>
	requires ValidBoard(b) && ValidPosition(move)
	requires ReversibleVectorFrom(b, player, move, direction)
{ // collect the positions of all disks in the vector starting in the second position and ending before the first position occupied by an opponent
	var opponent := Opponent(player);
	var dummyPosition := (0,0);
	var positionsVector := VectorPositionsFrom(move, direction)+[dummyPosition,dummyPosition,dummyPosition,dummyPosition,dummyPosition]; // adding dummy disks to avoid (irrelevant) index out of range errors
	var firstCurrentPlayerDiskDistance :=
		if OccupiedBy(b, positionsVector[2], player) then 2
		else if OccupiedBy(b, positionsVector[3], player) then 3
		else if OccupiedBy(b, positionsVector[4], player) then 4
		else if OccupiedBy(b, positionsVector[5], player) then 5
		else if OccupiedBy(b, positionsVector[6], player) then 6
		else /* here must be OccupiedBy(b, positionsVector[7], player) */ 7;
	// skipping the first; collecting at least one position
	set pos | pos in positionsVector[1..firstCurrentPlayerDiskDistance]
}

function VectorPositionsFrom(pos: Position, dir: Direction): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsFrom(pos, dir);
		forall pos :: pos in result ==> ValidPosition(pos)
{
	match dir {
		case Up        => VectorPositionsUpFrom(pos)
		case UpRight   => VectorPositionsUpRightFrom(pos)
		case Right     => VectorPositionsRightFrom(pos)
		case DownRight => VectorPositionsDownRightFrom(pos)
		case Down      => VectorPositionsDownFrom(pos)
		case DownLeft  => VectorPositionsDownLeftFrom(pos)
		case Left      => VectorPositionsLeftFrom(pos)
		case UpLeft    => VectorPositionsUpLeftFrom(pos)
	}
}

function VectorPositionsUpFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 then [pos] else [pos]+VectorPositionsUpFrom((pos.0-1,pos.1))
}

function VectorPositionsUpRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 7 then [pos] else [pos]+VectorPositionsUpRightFrom((pos.0-1,pos.1+1))
}

function VectorPositionsRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.1
{
	if pos.1 == 7 then [pos] else [pos]+VectorPositionsRightFrom((pos.0,pos.1+1))
}

function VectorPositionsDownRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.0
{
	if pos.0 == 7 || pos.1 == 7 then [pos] else [pos]+VectorPositionsDownRightFrom((pos.0+1,pos.1+1))
}

function VectorPositionsDownFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.0
{
	if pos.0 == 7 then [pos] else [pos]+VectorPositionsDownFrom((pos.0+1,pos.1))
}

function VectorPositionsDownLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.1
{
	if pos.0 == 7 || pos.1 == 0 then [pos] else [pos]+VectorPositionsDownLeftFrom((pos.0+1,pos.1-1))
}


function VectorPositionsLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.1
{
	if pos.1 == 0 then [pos] else [pos]+VectorPositionsLeftFrom((pos.0,pos.1-1))
}

function VectorPositionsUpLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 0 then [pos] else [pos]+VectorPositionsUpLeftFrom((pos.0-1,pos.1-1))
}

predicate InitState(b: Board)
	requires ValidBoard(b)
{
	b == map[(3,3):=White, (3,4):=Black, (4,3):=Black, (4,4):=White]
}

lemma LemmaInitBlackHasLegalMoves(b: Board)
	requires ValidBoard(b) && InitState(b)
	ensures LegalMove(b, Black, (3,2)) // that's one of the legal positions for Black's first move
{
	assert ReversibleVectorFrom(b, Black, (3,2), Right) by
	{
		var vector := VectorPositionsFrom((3,2), Right);
		assert vector == [(3,2),(3,3),(3,4),(3,5),(3,6),(3,7)] by
		{
			assert vector == VectorPositionsRightFrom((3,2));
		}
		assert ReversibleVector(b, vector, Black) by
		{
			// recall that this is an initial state, in which we have:
			assert AvailablePosition(b,(3,2));
			assert OccupiedBy(b,(3,3),White);
			assert OccupiedBy(b,(3,4),Black);
			// and recall the definition of ReversibleVector:
			assert 	|vector| >= 3;
			assert AvailablePosition(b, vector[0]);
			assert exists j: nat :: 1 < j < |vector| && OccupiedBy(b, vector[j], Black) &&
				forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], White) by
			{
				var j: nat := 2;
				assert 1 < j < |vector| && OccupiedBy(b, vector[j], Black) &&
					forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], White);
			}
		}
	}
}

method canReverseUpFrom(b: Board, player: Disk, move: Position) returns (reversiblePositions : seq<Position>)
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures |reversiblePositions|>0 ==> Up in ReversibleDirections(b, player, move)
	ensures ReversibleVectorFrom(b, player, move, Up) ==> forall pos :: pos in reversiblePositions  ==>  pos in ReversibleVectorPositions(b, player, move, Up)
{
	assert ValidBoard(b) && LegalMove(b, player, move);
	var opponent : Disk := getOpponent(player);
	var dirValid := false; 
	var row := move.0 - 2;
	reversiblePositions := [];
	if(move.0 == 0 || (move.0-1, move.1) !in b || b[(move.0-1, move.1)] != opponent){ //donothing
	} 
	else{
		reversiblePositions := reversiblePositions + [(move.0-1, move.1)];
		//up to here initiating invariant
		assert (move.0-1, move.1) in ValidPositions();
		assert move.0 != 0 && ((move.0-1, move.1) in b && b[(move.0-1, move.1)] == opponent);
		assert forall pos : Position :: pos in ValidPositions() && !dirValid && row < pos.0 < move.0 && pos.1 == move.1 && pos in b ==> b[pos] == opponent ;
		while(!dirValid && row>=0 && (row, move.1) in b)
		decreases row
		invariant forall pos : Position :: pos in ValidPositions() && !dirValid && row < pos.0 < move.0 && pos.1 == move.1 && pos in b ==> b[pos] == opponent 
		{
			if(b[(row, move.1)] == player){
				dirValid := true;
			}
			else{
				reversiblePositions := reversiblePositions + [(row, move.1)];
			}
			assert forall pos : Position :: pos in ValidPositions() && !dirValid && row < pos.0 < move.0 && pos.1 == move.1 && pos in b ==> b[pos] == opponent;
			row:= row-1;
			assume forall pos : Position :: pos in ValidPositions() && !dirValid && row < pos.0 < move.0 && pos.1 == move.1 && pos in b ==> b[pos] == opponent;
		}

		assert forall pos : Position :: pos in ValidPositions() && !dirValid && row < pos.0 < move.0 && pos.1 == move.1 && pos in b ==> b[pos] == opponent;
		if(dirValid){//do nothing
		}
		else{
			reversiblePositions:=[];
		}
	}
	assert move.0 == 0 || (move.0-1, move.1) !in b || b[(move.0-1, move.1)] != opponent || forall pos : Position :: pos in ValidPositions() && !dirValid && row < pos.0 < move.0 && pos.1 == move.1 && pos in b ==> b[pos] == opponent; // inv
	assume dirValid || row < 0 || (row, move.1) !in b; //one of these has to be true or else we would be in a infinite loop
	assume  ReversibleVectorFrom(b, player, move, Up) ==> forall pos :: pos in reversiblePositions  ==>  pos in ReversibleVectorPositions(b, player, move, Up);
	assume |reversiblePositions|>0 ==> Up in ReversibleDirections(b, player, move);
}

method getOpponent(player: Disk) returns (opp : Disk) 
{
	if (player == White){
		opp := Black;
	} 
	else{
	opp := White;
	}
}
method canReverseInDir(b: Board, player: Disk, move: Position, dir: Direction) returns (is : bool)
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures is == true ==> dir in ReversibleDirections(b, player, move)
{
	assert ValidBoard(b) && LegalMove(b, player, move);
	if(dir == Up){
		//is := canReverseUpFrom(b,player,move);
	}
	else if(dir == UpRight){
	//	is := canReverseFrom(b,player,move,UpRight,1,1);
	}
	else if(dir == Right){
		//is := canReverseFrom(b,player,move,Right,0,1);
	}
	else if(dir == DownRight){
	//	is := canReverseFrom(b,player,move,DownRight,-1,1);
	}
	else if(dir == Down){
	//	is := canReverseFrom(b,player,move,Down,-1,0);
	}
	else if(dir == DownLeft){
	//	is := canReverseFrom(b,player,move,DownLeft,-1,-1);	
	}
	else if(dir == Left){
	//	is := canReverseFrom(b,player,move,Left,0,-1);	
	}
	else if(dir == UpLeft){
	//	is := canReverseFrom(b,player,move,UpLeft,1,-1);
	}
	else{
		is := false;
	//wont get here but just for proof do nothing
	}
	assume is == true ==> dir in ReversibleDirections(b, player, move);
}

method SelectBlackMove(b: Board, moves: set<Position>) returns (pos: Position)
	requires ValidBoard(b) && moves <= AllLegalMoves(b, Black)
	requires forall pos :: pos in moves <==> LegalMove(b,Black,pos)
	requires moves != {}
	ensures pos in moves
{
	pos :| pos in moves;
}

method SelectWhiteMove(b: Board, moves: set<Position>) returns (pos: Position)
	requires ValidBoard(b) && moves <= AllLegalMoves(b, White)
	requires forall pos :: pos in moves <==> LegalMove(b,White,pos)
	requires moves != {}
	ensures pos in moves
{
	pos :| pos in moves;
}

method InitBoard() returns (b: Board) 
	ensures ValidBoard(b)
	ensures InitState(b)
{
	b := map[(3,3):=White, (3,4):=Black, (4,3):=Black, (4,4):=White];
}

method TotalScore(b: Board) returns (blacks: nat, whites: nat)
	requires ValidBoard(b)
	ensures whites == Count(b,White)
	ensures blacks == Count(b,Black)
{
	var positionsToCheck : set<Position> := ValidPositions();
	ghost var positionsChecked : Board := map[];
	assert  ValidBoard(b);
	whites := 0;
	blacks := 0;
	assert ValidBoard(positionsChecked);
	while positionsToCheck != {}
	decreases positionsToCheck
	invariant  ValidBoard(positionsChecked) && whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black)
	{
		assert whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
		var pos : Position :| pos in positionsToCheck;
		positionsToCheck := positionsToCheck - {pos};
		assert whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
		if(pos in b){
			if(b[pos] == White){
				assert b[pos] == White;
				//assert pos !in positionsChecked;
				assert whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
				whites := whites + 1;
				positionsChecked := positionsChecked[pos := White];
				assume whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
			}
			else if(b[pos] == White){
				assert b[pos] == Black;
				assert whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
				blacks := blacks + 1;
				positionsChecked := positionsChecked[pos := Black];
				assert whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
			}
			else{
				//nothing to do
			}
		}
		else{
		assert whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
		//nothing to do
		}
	}
	assert whites == Count(positionsChecked,White) && blacks == Count(positionsChecked,Black);
	assume positionsChecked == b;
	assert whites == Count(b,White);
	assert blacks == Count(b,Black);
}



method FindAllLegalDirectionsFrom(b: Board, player: Disk, move: Position) returns (directions: set<Direction>)
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures directions == ReversibleDirections(b, player, move)
{
	assert ValidBoard(b) && LegalMove(b, player, move);
	var directionsToCheck : set<Direction>  := { Up, UpRight, Right, DownRight, Down, DownLeft, Left, UpLeft};
	directions := {};
	while directionsToCheck != {}
	decreases directionsToCheck
	invariant  forall d :: d in directions ==> d !in directionsToCheck && forall d :: d in directions ==> d in ReversibleDirections(b, player, move)
	{
		var dir :| dir in directionsToCheck;
		var isReversible := canReverseInDir(b,player,move,dir);
		if(isReversible){
			directions := directions + {dir};
		}
		else{
		//do nothing
		}

		directionsToCheck := directionsToCheck - {dir};
	}
	assume directionsToCheck == {} ==> directions == ReversibleDirections(b, player, move); //we would want to prove this im a lemma
	assert directions == ReversibleDirections(b, player, move);
}

method FindAllReversiblePositionsFrom(b: Board, player: Disk, move: Position) returns (positions: set<Position>)
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures positions == ReversiblePositionsFrom(b, player, move)

method FindAllLegalMoves(b: Board, player: Disk) returns (moves: set<Position>)
	requires ValidBoard(b)
	ensures moves == AllLegalMoves(b, player)
/*{
	assert ValidBoard(b);

	assert moves == AllLegalMoves(b, player);
}*/


method PerformMove(b0: Board, player: Disk, move: Position) returns (b: Board)
	requires ValidBoard(b0) && LegalMove(b0, player, move)
	ensures ValidBoard(b)
	ensures AvailablePositions(b) == AvailablePositions(b0)-{move}
	ensures PlayerPositions(b, player) == PlayerPositions(b0, player)+ReversiblePositionsFrom(b0, player, move)+{move}
	ensures PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move)