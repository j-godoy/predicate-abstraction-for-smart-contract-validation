// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

// estados concretos
abstract sig EstadoConcreto {
	_player1: Address,
	_player2: Address,
	_owner: Address,
	_p1Choice: Int,
	_p2Choice: Int,
	_payoffMatrix: Int->Int->Int,
	_balance: Address->Int
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


abstract sig Address{}
one sig Address0x0 extends Address{}
one sig Address1 extends Address{}
one sig Address2 extends Address{}
one sig Address3 extends Address{}

pred invariante[e:EstadoConcreto] {
}


pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, value: Int, player1: Address, player2: Address, owner: Address] {
	//PRE
	no ein._payoffMatrix
	no ein._p1Choice
	no ein._p2Choice
	ein._p1Choice = -1
	ein._p2Choice = -1

	//POST
	eout._player1 = player1
	eout._player2 = player2
	eout._owner = owner
	#eout._balance = 4
	(all a:Address | eout._balance[a] = 0)

        //Rock - 0
        //Paper - 1
        //Scissors - 2
	eout._payoffMatrix = ein._payoffMatrix++0->0->0
	eout._payoffMatrix = ein._payoffMatrix++0->1->2
	eout._payoffMatrix = ein._payoffMatrix++0->2->1
	eout._payoffMatrix = ein._payoffMatrix++1->0->1
	eout._payoffMatrix = ein._payoffMatrix++1->1->0
	eout._payoffMatrix = ein._payoffMatrix++1->2->2
	eout._payoffMatrix = ein._payoffMatrix++2->0->2
	eout._payoffMatrix = ein._payoffMatrix++2->1->1
	eout._payoffMatrix = ein._payoffMatrix++2->2->0

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
pred partitionS00[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._payoffMatrix
	e._p1Choice = -1 and e._p2Choice = -1
}


pred partitionINV[e: EstadoConcreto]{
	not invariante[e]
}

pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and not pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and pre_choicePlayer2[e] and not pre_determineWinner[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and not pre_choicePlayer2[e] and not pre_determineWinner[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and not pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and pre_choicePlayer2[e] and not pre_determineWinner[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and not pre_choicePlayer2[e] and not pre_determineWinner[e]
}

pred transicion_S00_a_S00_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S06_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S07_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_S08_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S03_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S04_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S05_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S06_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S07_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_S08_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S01_a_INV_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S03_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S04_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S05_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S06_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S07_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_S08_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S02_a_INV_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S00_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S01_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S02_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S03_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S04_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S05_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S06_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S07_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_S08_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S03_a_INV_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S00_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S01_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S02_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S03_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S04_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S05_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S06_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S07_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_S08_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S04_a_INV_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S00_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S01_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S02_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S03_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S04_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S05_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S06_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S07_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_S08_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S05_a_INV_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S00_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S01_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S02_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S03_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S04_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S05_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S06_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S07_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_S08_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S06_a_INV_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S00_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S01_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S02_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S03_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S04_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S05_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S06_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S07_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_S08_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S07_a_INV_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S00_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S01_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S02_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S03_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S04_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S05_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S06_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S07_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_S08_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

pred transicion_S08_a_INV_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Int, v20, v21, v22:Address | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22])
}

run transicion_S00_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_constructor for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S04_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S05_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S06_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S07_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S08_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_INV_mediante_met_choicePlayer1{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_choicePlayer1{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_choicePlayer1{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_choicePlayer1{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S00_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_choicePlayer1{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S00_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_choicePlayer1{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S00_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_INV_mediante_met_choicePlayer1{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S00_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_INV_mediante_met_choicePlayer1{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S00_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_INV_mediante_met_choicePlayer1{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer1 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S00_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S07_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S00_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_choicePlayer1 for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_choicePlayer1 for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S04_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S05_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S06_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S07_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S08_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_INV_mediante_met_choicePlayer2{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_choicePlayer2{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_choicePlayer2{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_choicePlayer2{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S00_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_choicePlayer2{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S00_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_choicePlayer2{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S00_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_INV_mediante_met_choicePlayer2{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S00_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_INV_mediante_met_choicePlayer2{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S00_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_INV_mediante_met_choicePlayer2{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_choicePlayer2 [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S00_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S07_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S00_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_choicePlayer2 for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_choicePlayer2 for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_determineWinner{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_determineWinner{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_determineWinner{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_determineWinner{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_determineWinner{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_determineWinner{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_determineWinner{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_determineWinner{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_determineWinner{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_determineWinner [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S07_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S00_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_determineWinner for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_determineWinner for 2 EstadoConcreto
