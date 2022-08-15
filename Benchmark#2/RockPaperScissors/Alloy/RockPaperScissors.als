// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

// estados concretos
abstract sig EstadoConcreto {
	_player1: lone Address,
	_player2: lone Address,
	_owner: lone Address,
	_p1Choice: Int,
	_p2Choice: Int,
	_payoffMatrix: Int->Int->Int,
	_balance: Address->Int
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}

//run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto

abstract sig Address{}
one sig Address0x0 extends Address{}
one sig Address1 extends Address{}
one sig Address2 extends Address{}
one sig Address3 extends Address{}

pred invariante[e:EstadoConcreto] {
	e._p1Choice >= -1 and e._p1Choice <= 2
	e._p2Choice >= -1 and e._p2Choice <= 2
	
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	
	e._owner != e._player1 and e._owner != e._player2 and e._player1 != e._player2
	
}


pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, value: Int, player1: Address, player2: Address, owner: Address] {
	//PRE
	no ein._player1
	no ein._player2
	ein._p1Choice = -1
	ein._p2Choice = -1
	player1 != Address0x0
	player2 != Address0x0
	owner != Address0x0

	//POST
	eout._player1 = player1
	eout._player2 = player2
	eout._owner = owner
	eout._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	//#eout._balance = 4
	//(all a:Address | eout._balance[a] = 0)

        //Rock - 0
        //Paper - 1
        //Scissors - 2
	/*
	eout._payoffMatrix = ein._payoffMatrix++0->0->0
	eout._payoffMatrix = ein._payoffMatrix++0->1->2
	eout._payoffMatrix = ein._payoffMatrix++0->2->1
	eout._payoffMatrix = ein._payoffMatrix++1->0->1
	eout._payoffMatrix = ein._payoffMatrix++1->1->0
	eout._payoffMatrix = ein._payoffMatrix++1->2->2
	eout._payoffMatrix = ein._payoffMatrix++2->0->2
	eout._payoffMatrix = ein._payoffMatrix++2->1->1
	eout._payoffMatrix = ein._payoffMatrix++2->2->0
	*/

	eout._p1Choice = ein._p1Choice
	eout._p2Choice = ein._p2Choice
	//eout._player1 = ein._player1
	//eout._player2 = ein._player2
	//eout._owner = ein._owner
	//eout._payoffMatrix = ein._payoffMatrix
	eout._balance = ein._balance
}

pred pre_choicePlayer1[e: EstadoConcreto] {
	e._p1Choice = -1
}

pred met_choicePlayer1[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, choice: Int, value: Int] {
	//PRE
	pre_choicePlayer1[ein]
	sender = ein._player1
	sender != Address0x0
	choice >= 0 and choice <= 2


	//POST
	eout._p1Choice = choice
	eout._balance = ein._balance++Address0x0->ein._balance[Address0x0].add[value]

	//eout._p1Choice = ein._p1Choice
	eout._p2Choice = ein._p2Choice
	eout._player1 = ein._player1
	eout._player2 = ein._player2
	eout._owner = ein._owner
	eout._payoffMatrix = ein._payoffMatrix
	//eout._balance = ein._balance
}

pred pre_choicePlayer2[e: EstadoConcreto] {
	e._p2Choice = -1
}

pred met_choicePlayer2[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, choice: Int, value: Int] {
	//PRE
	pre_choicePlayer2[ein]
	sender = ein._player2
	sender != Address0x0
	choice >= 0 and choice <= 2


	//POST
	eout._p2Choice = choice
	eout._balance = ein._balance++Address0x0->ein._balance[Address0x0].add[value]

	eout._p1Choice = ein._p1Choice
	//eout._p2Choice = ein._p2Choice
	eout._player1 = ein._player1
	eout._player2 = ein._player2
	eout._owner = ein._owner
	eout._payoffMatrix = ein._payoffMatrix
	eout._balance = ein._balance
}

pred pre_determineWinner[e:EstadoConcreto] {
	e._p1Choice != -1 and e._p2Choice != -1
}

pred met_determineWinner[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_determineWinner[ein]
	
	//POST
	(let winner = (ein._payoffMatrix[ein._p1Choice])[ein._p2Choice] |
			(winner = 1) => eout._balance = ein._balance++Address1->ein._balance[Address0x0]
		else
			(winner = 2) => eout._balance = ein._balance++Address2->ein._balance[Address0x0]
            	else
			(winner = 0) => eout._balance = ein._balance++ein._owner->ein._balance[Address0x0]
	)

	eout._balance = ein._balance++Address0x0->0

	eout._p1Choice = ein._p1Choice
	eout._p2Choice = ein._p2Choice
	eout._player1 = ein._player1
	eout._player2 = ein._player2
	eout._owner = ein._owner
	eout._payoffMatrix = ein._payoffMatrix
}

pred isWinner[user: Address, e:EstadoConcreto] {
	(let winner = (e._payoffMatrix[e._p1Choice])[e._p2Choice] |
			(winner = 1) => user = e._player1
		else
			(winner = 2) => user = e._player2
            	else
			(winner = 0) => user = e._owner
	)
}

//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{ // Init
	//(invariante[e])
	no e._player1
	no e._player2
	no e._owner
	e._p1Choice = -1
	e._p2Choice = -1
}

pred partitionS01[e: EstadoConcreto]{ // Sin apuestas
	(invariante[e])
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	e._p1Choice = -1 and e._p2Choice = -1
	some e._player1
	some e._player2
	some e._owner
}
run invariante
pred partitionS02[e: EstadoConcreto]{ // Apuesta1
	(invariante[e])
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	e._p1Choice != -1 and e._p2Choice = -1
	some e._player1
	some e._player2
	some e._owner
}

pred partitionS03[e: EstadoConcreto]{ // Apuesta2
	(invariante[e])
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	e._p1Choice = -1 and e._p2Choice != -1
	some e._player1
	some e._player2
	some e._owner
}

pred partitionS04[e: EstadoConcreto]{ // apuestan ambos, gana1
	(invariante[e])
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	e._p1Choice != -1 and e._p2Choice != -1
	some e._player1
	some e._player2
	isWinner[e._player1, e]
}

pred partitionS05[e: EstadoConcreto]{ // apuestan ambos, gana2
	(invariante[e])
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	e._p1Choice != -1 and e._p2Choice != -1
	some e._player1
	some e._player2
	some e._owner
	isWinner[e._player2, e]
}

pred partitionS06[e: EstadoConcreto]{ // apuestan ambos, empate->gana Owner
	(invariante[e])
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	e._p1Choice != -1 and e._p2Choice != -1
	some e._player1
	some e._player2
	some e._owner
	isWinner[e._owner, e]
}

pred partitionINV[e: EstadoConcreto]{ // 
	(not invariante[e])
}







pred transicion_S00_a_S01_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | v20 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | v20 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | v20 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | v20 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | v20 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S06_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | v20 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | v20 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto
pred transicion_S01_a_S01_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_INV_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
pred transicion_S01_a_S01_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_INV_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
pred transicion_S01_a_S01_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S01_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
