// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{balance: Int}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressBeneficiary extends Address{}

// estados concretos
abstract sig EstadoConcreto {
	_owner: Address,
	_maxBlock: Int,
	_goal: Int,
	_backers: Backer,
	_funded: Bool,
	_balance: Int,
	_blockNumber: Int //lo agrego para simular el paso del tiempo
}

sig Backer{b: Address->Int}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}

//run transicion_S05_a_S06_mediante_met_donate for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
//run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq

fun LIMIT[]: Int {3}

pred invariante [e:EstadoConcreto] {
	//Mientras esté en periodo de aportes, la suma de depósitos debe ser igual al balance
	//e._blockNumber <= e._maxBlock implies e._balance = sumatoria[e]
	e._blockNumber <= e._maxBlock implies sumatoria[e._backers, e._balance]

	//Si se terminó el tiempo, debe suceder que balance <= sumaDepósitos
	//Más especificamente, balance debe ser igual sumatoria de sumaDepósitos para k elementos (0<=k<#backers)
	e._blockNumber > e._maxBlock implies ((e._funded = True and e._balance = 0) or sumatoriaSubSeq[e._backers, e._balance])

	//Si funded=true, entonces balance = 0
	e._funded = True implies (e._balance = 0 and e._blockNumber > e._maxBlock)

	//No Negativos
	e._balance >= 0 and e._blockNumber >= 0 and e._maxBlock >= 0 and e._goal >= 0
	all d0:Address | e._backers.b[d0] >= 0

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._backers.b[d0] >= 0 and e._backers.b[d0] <= LIMIT[]
	#(e._backers.b.Int) <= 4
}

pred notInvariante[e: EstadoConcreto]{
	(not invariante[e])
	some sumaSeq: SumatoriaSeq, suma: Int | toSeq[e._backers, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}


fun sumof[s:seq Int]: Int {
	s=none->none implies 0
	else s=0->0 implies 0
	else s=0->1 implies 1
	else s=0->2 implies 2
	else s=0->3 implies 3
	else s=0->0+1->0 implies 0
	else s=0->0+1->1 implies 1
	else s=0->0+1->2 implies 2
	else s=0->0+1->3 implies 3
	else s=0->1+1->0 implies 1
	else s=0->1+1->1 implies 2
	else s=0->1+1->2 implies 3
	else s=0->1+1->3 implies 4
	else s=0->2+1->0 implies 2
	else s=0->2+1->1 implies 3
	else s=0->2+1->2 implies 4
	else s=0->2+1->3 implies 5
	else s=0->3+1->0 implies 3
	else s=0->3+1->1 implies 4
	else s=0->3+1->2 implies 5
	else s=0->3+1->3 implies 6
	else s=0->0+1->0+2->0 implies 0
	else s=0->0+1->0+2->1 implies 1
	else s=0->0+1->0+2->2 implies 2
	else s=0->0+1->0+2->3 implies 3
	else s=0->0+1->1+2->0 implies 1
	else s=0->0+1->1+2->1 implies 2
	else s=0->0+1->1+2->2 implies 3
	else s=0->0+1->1+2->3 implies 4
	else s=0->0+1->2+2->0 implies 2
	else s=0->0+1->2+2->1 implies 3
	else s=0->0+1->2+2->2 implies 4
	else s=0->0+1->2+2->3 implies 5
	else s=0->0+1->3+2->0 implies 3
	else s=0->0+1->3+2->1 implies 4
	else s=0->0+1->3+2->2 implies 5
	else s=0->0+1->3+2->3 implies 6
	else s=0->1+1->0+2->0 implies 1
	else s=0->1+1->0+2->1 implies 2
	else s=0->1+1->0+2->2 implies 3
	else s=0->1+1->0+2->3 implies 4
	else s=0->1+1->1+2->0 implies 2
	else s=0->1+1->1+2->1 implies 3
	else s=0->1+1->1+2->2 implies 4
	else s=0->1+1->1+2->3 implies 5
	else s=0->1+1->2+2->0 implies 3
	else s=0->1+1->2+2->1 implies 4
	else s=0->1+1->2+2->2 implies 5
	else s=0->1+1->2+2->3 implies 6
	else s=0->1+1->3+2->0 implies 4
	else s=0->1+1->3+2->1 implies 5
	else s=0->1+1->3+2->2 implies 6
	else s=0->1+1->3+2->3 implies 7
	else s=0->2+1->0+2->0 implies 2
	else s=0->2+1->0+2->1 implies 3
	else s=0->2+1->0+2->2 implies 4
	else s=0->2+1->0+2->3 implies 5
	else s=0->2+1->1+2->0 implies 3
	else s=0->2+1->1+2->1 implies 4
	else s=0->2+1->1+2->2 implies 5
	else s=0->2+1->1+2->3 implies 6
	else s=0->2+1->2+2->0 implies 4
	else s=0->2+1->2+2->1 implies 5
	else s=0->2+1->2+2->2 implies 6
	else s=0->2+1->2+2->3 implies 7
	else s=0->2+1->3+2->0 implies 5
	else s=0->2+1->3+2->1 implies 6
	else s=0->2+1->3+2->2 implies 7
	else s=0->2+1->3+2->3 implies 8
	else s=0->3+1->0+2->0 implies 3
	else s=0->3+1->0+2->1 implies 4
	else s=0->3+1->0+2->2 implies 5
	else s=0->3+1->0+2->3 implies 6
	else s=0->3+1->1+2->0 implies 4
	else s=0->3+1->1+2->1 implies 5
	else s=0->3+1->1+2->2 implies 6
	else s=0->3+1->1+2->3 implies 7
	else s=0->3+1->2+2->0 implies 5
	else s=0->3+1->2+2->1 implies 6
	else s=0->3+1->2+2->2 implies 7
	else s=0->3+1->2+2->3 implies 8
	else s=0->3+1->3+2->0 implies 6
	else s=0->3+1->3+2->1 implies 7
	else s=0->3+1->3+2->2 implies 8
	else s=0->3+1->3+2->3 implies 9
	else s=0->0+1->0+2->0+3->0 implies 0
	else s=0->0+1->0+2->0+3->1 implies 1
	else s=0->0+1->0+2->0+3->2 implies 2
	else s=0->0+1->0+2->0+3->3 implies 3
	else s=0->0+1->0+2->1+3->0 implies 1
	else s=0->0+1->0+2->1+3->1 implies 2
	else s=0->0+1->0+2->1+3->2 implies 3
	else s=0->0+1->0+2->1+3->3 implies 4
	else s=0->0+1->0+2->2+3->0 implies 2
	else s=0->0+1->0+2->2+3->1 implies 3
	else s=0->0+1->0+2->2+3->2 implies 4
	else s=0->0+1->0+2->2+3->3 implies 5
	else s=0->0+1->0+2->3+3->0 implies 3
	else s=0->0+1->0+2->3+3->1 implies 4
	else s=0->0+1->0+2->3+3->2 implies 5
	else s=0->0+1->0+2->3+3->3 implies 6
	else s=0->0+1->1+2->0+3->0 implies 1
	else s=0->0+1->1+2->0+3->1 implies 2
	else s=0->0+1->1+2->0+3->2 implies 3
	else s=0->0+1->1+2->0+3->3 implies 4
	else s=0->0+1->1+2->1+3->0 implies 2
	else s=0->0+1->1+2->1+3->1 implies 3
	else s=0->0+1->1+2->1+3->2 implies 4
	else s=0->0+1->1+2->1+3->3 implies 5
	else s=0->0+1->1+2->2+3->0 implies 3
	else s=0->0+1->1+2->2+3->1 implies 4
	else s=0->0+1->1+2->2+3->2 implies 5
	else s=0->0+1->1+2->2+3->3 implies 6
	else s=0->0+1->1+2->3+3->0 implies 4
	else s=0->0+1->1+2->3+3->1 implies 5
	else s=0->0+1->1+2->3+3->2 implies 6
	else s=0->0+1->1+2->3+3->3 implies 7
	else s=0->0+1->2+2->0+3->0 implies 2
	else s=0->0+1->2+2->0+3->1 implies 3
	else s=0->0+1->2+2->0+3->2 implies 4
	else s=0->0+1->2+2->0+3->3 implies 5
	else s=0->0+1->2+2->1+3->0 implies 3
	else s=0->0+1->2+2->1+3->1 implies 4
	else s=0->0+1->2+2->1+3->2 implies 5
	else s=0->0+1->2+2->1+3->3 implies 6
	else s=0->0+1->2+2->2+3->0 implies 4
	else s=0->0+1->2+2->2+3->1 implies 5
	else s=0->0+1->2+2->2+3->2 implies 6
	else s=0->0+1->2+2->2+3->3 implies 7
	else s=0->0+1->2+2->3+3->0 implies 5
	else s=0->0+1->2+2->3+3->1 implies 6
	else s=0->0+1->2+2->3+3->2 implies 7
	else s=0->0+1->2+2->3+3->3 implies 8
	else s=0->0+1->3+2->0+3->0 implies 3
	else s=0->0+1->3+2->0+3->1 implies 4
	else s=0->0+1->3+2->0+3->2 implies 5
	else s=0->0+1->3+2->0+3->3 implies 6
	else s=0->0+1->3+2->1+3->0 implies 4
	else s=0->0+1->3+2->1+3->1 implies 5
	else s=0->0+1->3+2->1+3->2 implies 6
	else s=0->0+1->3+2->1+3->3 implies 7
	else s=0->0+1->3+2->2+3->0 implies 5
	else s=0->0+1->3+2->2+3->1 implies 6
	else s=0->0+1->3+2->2+3->2 implies 7
	else s=0->0+1->3+2->2+3->3 implies 8
	else s=0->0+1->3+2->3+3->0 implies 6
	else s=0->0+1->3+2->3+3->1 implies 7
	else s=0->0+1->3+2->3+3->2 implies 8
	else s=0->0+1->3+2->3+3->3 implies 9
	else s=0->1+1->0+2->0+3->0 implies 1
	else s=0->1+1->0+2->0+3->1 implies 2
	else s=0->1+1->0+2->0+3->2 implies 3
	else s=0->1+1->0+2->0+3->3 implies 4
	else s=0->1+1->0+2->1+3->0 implies 2
	else s=0->1+1->0+2->1+3->1 implies 3
	else s=0->1+1->0+2->1+3->2 implies 4
	else s=0->1+1->0+2->1+3->3 implies 5
	else s=0->1+1->0+2->2+3->0 implies 3
	else s=0->1+1->0+2->2+3->1 implies 4
	else s=0->1+1->0+2->2+3->2 implies 5
	else s=0->1+1->0+2->2+3->3 implies 6
	else s=0->1+1->0+2->3+3->0 implies 4
	else s=0->1+1->0+2->3+3->1 implies 5
	else s=0->1+1->0+2->3+3->2 implies 6
	else s=0->1+1->0+2->3+3->3 implies 7
	else s=0->1+1->1+2->0+3->0 implies 2
	else s=0->1+1->1+2->0+3->1 implies 3
	else s=0->1+1->1+2->0+3->2 implies 4
	else s=0->1+1->1+2->0+3->3 implies 5
	else s=0->1+1->1+2->1+3->0 implies 3
	else s=0->1+1->1+2->1+3->1 implies 4
	else s=0->1+1->1+2->1+3->2 implies 5
	else s=0->1+1->1+2->1+3->3 implies 6
	else s=0->1+1->1+2->2+3->0 implies 4
	else s=0->1+1->1+2->2+3->1 implies 5
	else s=0->1+1->1+2->2+3->2 implies 6
	else s=0->1+1->1+2->2+3->3 implies 7
	else s=0->1+1->1+2->3+3->0 implies 5
	else s=0->1+1->1+2->3+3->1 implies 6
	else s=0->1+1->1+2->3+3->2 implies 7
	else s=0->1+1->1+2->3+3->3 implies 8
	else s=0->1+1->2+2->0+3->0 implies 3
	else s=0->1+1->2+2->0+3->1 implies 4
	else s=0->1+1->2+2->0+3->2 implies 5
	else s=0->1+1->2+2->0+3->3 implies 6
	else s=0->1+1->2+2->1+3->0 implies 4
	else s=0->1+1->2+2->1+3->1 implies 5
	else s=0->1+1->2+2->1+3->2 implies 6
	else s=0->1+1->2+2->1+3->3 implies 7
	else s=0->1+1->2+2->2+3->0 implies 5
	else s=0->1+1->2+2->2+3->1 implies 6
	else s=0->1+1->2+2->2+3->2 implies 7
	else s=0->1+1->2+2->2+3->3 implies 8
	else s=0->1+1->2+2->3+3->0 implies 6
	else s=0->1+1->2+2->3+3->1 implies 7
	else s=0->1+1->2+2->3+3->2 implies 8
	else s=0->1+1->2+2->3+3->3 implies 9
	else s=0->1+1->3+2->0+3->0 implies 4
	else s=0->1+1->3+2->0+3->1 implies 5
	else s=0->1+1->3+2->0+3->2 implies 6
	else s=0->1+1->3+2->0+3->3 implies 7
	else s=0->1+1->3+2->1+3->0 implies 5
	else s=0->1+1->3+2->1+3->1 implies 6
	else s=0->1+1->3+2->1+3->2 implies 7
	else s=0->1+1->3+2->1+3->3 implies 8
	else s=0->1+1->3+2->2+3->0 implies 6
	else s=0->1+1->3+2->2+3->1 implies 7
	else s=0->1+1->3+2->2+3->2 implies 8
	else s=0->1+1->3+2->2+3->3 implies 9
	else s=0->1+1->3+2->3+3->0 implies 7
	else s=0->1+1->3+2->3+3->1 implies 8
	else s=0->1+1->3+2->3+3->2 implies 9
	else s=0->1+1->3+2->3+3->3 implies 10
	else s=0->2+1->0+2->0+3->0 implies 2
	else s=0->2+1->0+2->0+3->1 implies 3
	else s=0->2+1->0+2->0+3->2 implies 4
	else s=0->2+1->0+2->0+3->3 implies 5
	else s=0->2+1->0+2->1+3->0 implies 3
	else s=0->2+1->0+2->1+3->1 implies 4
	else s=0->2+1->0+2->1+3->2 implies 5
	else s=0->2+1->0+2->1+3->3 implies 6
	else s=0->2+1->0+2->2+3->0 implies 4
	else s=0->2+1->0+2->2+3->1 implies 5
	else s=0->2+1->0+2->2+3->2 implies 6
	else s=0->2+1->0+2->2+3->3 implies 7
	else s=0->2+1->0+2->3+3->0 implies 5
	else s=0->2+1->0+2->3+3->1 implies 6
	else s=0->2+1->0+2->3+3->2 implies 7
	else s=0->2+1->0+2->3+3->3 implies 8
	else s=0->2+1->1+2->0+3->0 implies 3
	else s=0->2+1->1+2->0+3->1 implies 4
	else s=0->2+1->1+2->0+3->2 implies 5
	else s=0->2+1->1+2->0+3->3 implies 6
	else s=0->2+1->1+2->1+3->0 implies 4
	else s=0->2+1->1+2->1+3->1 implies 5
	else s=0->2+1->1+2->1+3->2 implies 6
	else s=0->2+1->1+2->1+3->3 implies 7
	else s=0->2+1->1+2->2+3->0 implies 5
	else s=0->2+1->1+2->2+3->1 implies 6
	else s=0->2+1->1+2->2+3->2 implies 7
	else s=0->2+1->1+2->2+3->3 implies 8
	else s=0->2+1->1+2->3+3->0 implies 6
	else s=0->2+1->1+2->3+3->1 implies 7
	else s=0->2+1->1+2->3+3->2 implies 8
	else s=0->2+1->1+2->3+3->3 implies 9
	else s=0->2+1->2+2->0+3->0 implies 4
	else s=0->2+1->2+2->0+3->1 implies 5
	else s=0->2+1->2+2->0+3->2 implies 6
	else s=0->2+1->2+2->0+3->3 implies 7
	else s=0->2+1->2+2->1+3->0 implies 5
	else s=0->2+1->2+2->1+3->1 implies 6
	else s=0->2+1->2+2->1+3->2 implies 7
	else s=0->2+1->2+2->1+3->3 implies 8
	else s=0->2+1->2+2->2+3->0 implies 6
	else s=0->2+1->2+2->2+3->1 implies 7
	else s=0->2+1->2+2->2+3->2 implies 8
	else s=0->2+1->2+2->2+3->3 implies 9
	else s=0->2+1->2+2->3+3->0 implies 7
	else s=0->2+1->2+2->3+3->1 implies 8
	else s=0->2+1->2+2->3+3->2 implies 9
	else s=0->2+1->2+2->3+3->3 implies 10
	else s=0->2+1->3+2->0+3->0 implies 5
	else s=0->2+1->3+2->0+3->1 implies 6
	else s=0->2+1->3+2->0+3->2 implies 7
	else s=0->2+1->3+2->0+3->3 implies 8
	else s=0->2+1->3+2->1+3->0 implies 6
	else s=0->2+1->3+2->1+3->1 implies 7
	else s=0->2+1->3+2->1+3->2 implies 8
	else s=0->2+1->3+2->1+3->3 implies 9
	else s=0->2+1->3+2->2+3->0 implies 7
	else s=0->2+1->3+2->2+3->1 implies 8
	else s=0->2+1->3+2->2+3->2 implies 9
	else s=0->2+1->3+2->2+3->3 implies 10
	else s=0->2+1->3+2->3+3->0 implies 8
	else s=0->2+1->3+2->3+3->1 implies 9
	else s=0->2+1->3+2->3+3->2 implies 10
	else s=0->2+1->3+2->3+3->3 implies 11
	else s=0->3+1->0+2->0+3->0 implies 3
	else s=0->3+1->0+2->0+3->1 implies 4
	else s=0->3+1->0+2->0+3->2 implies 5
	else s=0->3+1->0+2->0+3->3 implies 6
	else s=0->3+1->0+2->1+3->0 implies 4
	else s=0->3+1->0+2->1+3->1 implies 5
	else s=0->3+1->0+2->1+3->2 implies 6
	else s=0->3+1->0+2->1+3->3 implies 7
	else s=0->3+1->0+2->2+3->0 implies 5
	else s=0->3+1->0+2->2+3->1 implies 6
	else s=0->3+1->0+2->2+3->2 implies 7
	else s=0->3+1->0+2->2+3->3 implies 8
	else s=0->3+1->0+2->3+3->0 implies 6
	else s=0->3+1->0+2->3+3->1 implies 7
	else s=0->3+1->0+2->3+3->2 implies 8
	else s=0->3+1->0+2->3+3->3 implies 9
	else s=0->3+1->1+2->0+3->0 implies 4
	else s=0->3+1->1+2->0+3->1 implies 5
	else s=0->3+1->1+2->0+3->2 implies 6
	else s=0->3+1->1+2->0+3->3 implies 7
	else s=0->3+1->1+2->1+3->0 implies 5
	else s=0->3+1->1+2->1+3->1 implies 6
	else s=0->3+1->1+2->1+3->2 implies 7
	else s=0->3+1->1+2->1+3->3 implies 8
	else s=0->3+1->1+2->2+3->0 implies 6
	else s=0->3+1->1+2->2+3->1 implies 7
	else s=0->3+1->1+2->2+3->2 implies 8
	else s=0->3+1->1+2->2+3->3 implies 9
	else s=0->3+1->1+2->3+3->0 implies 7
	else s=0->3+1->1+2->3+3->1 implies 8
	else s=0->3+1->1+2->3+3->2 implies 9
	else s=0->3+1->1+2->3+3->3 implies 10
	else s=0->3+1->2+2->0+3->0 implies 5
	else s=0->3+1->2+2->0+3->1 implies 6
	else s=0->3+1->2+2->0+3->2 implies 7
	else s=0->3+1->2+2->0+3->3 implies 8
	else s=0->3+1->2+2->1+3->0 implies 6
	else s=0->3+1->2+2->1+3->1 implies 7
	else s=0->3+1->2+2->1+3->2 implies 8
	else s=0->3+1->2+2->1+3->3 implies 9
	else s=0->3+1->2+2->2+3->0 implies 7
	else s=0->3+1->2+2->2+3->1 implies 8
	else s=0->3+1->2+2->2+3->2 implies 9
	else s=0->3+1->2+2->2+3->3 implies 10
	else s=0->3+1->2+2->3+3->0 implies 8
	else s=0->3+1->2+2->3+3->1 implies 9
	else s=0->3+1->2+2->3+3->2 implies 10
	else s=0->3+1->2+2->3+3->3 implies 11
	else s=0->3+1->3+2->0+3->0 implies 6
	else s=0->3+1->3+2->0+3->1 implies 7
	else s=0->3+1->3+2->0+3->2 implies 8
	else s=0->3+1->3+2->0+3->3 implies 9
	else s=0->3+1->3+2->1+3->0 implies 7
	else s=0->3+1->3+2->1+3->1 implies 8
	else s=0->3+1->3+2->1+3->2 implies 9
	else s=0->3+1->3+2->1+3->3 implies 10
	else s=0->3+1->3+2->2+3->0 implies 8
	else s=0->3+1->3+2->2+3->1 implies 9
	else s=0->3+1->3+2->2+3->2 implies 10
	else s=0->3+1->3+2->2+3->3 implies 11
	else s=0->3+1->3+2->3+3->0 implies 9
	else s=0->3+1->3+2->3+3->1 implies 10
	else s=0->3+1->3+2->3+3->2 implies 11
	else s=0->3+1->3+2->3+3->3 implies 12
	else 0
}

pred sumatoria [s: set Backer, suma: Int] {
	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}

pred sumatoriaSubSeq [s: set Backer, suma: Int] {
	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
}

pred subSeq [original: seq Int, subseq: seq Int] {
	#subseq <= #original
	all i: Int | some subseq[i] implies subseq[i] in original.elems
	all i: Int | some subseq[i] implies #subseq.i <= #original.i
}

pred toSeq [s: set Backer, ret: seq Int] {
	all d0: s.b.Int | some i: Int | ret[i]=s.b[d0] //Todo elemento del set está en la seq
	all i: Int | some ret[i] implies some d0: s.b.Int | s.b[d0]=ret[i]//Todo elemento de la seq está en el set
	all i: Int | #(s.b.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
	#(s.b.Int)=#(ret)
}


run invariante

sig SumatoriaSeq {sec: seq Int}

pred met_constructor [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, owner: Address, value: Int, max_block: Int, goal: Int, timeElapsed: Int] {
	//Pre
	ein._owner = Address0x0
	ein._maxBlock = 0
	ein._goal = 0
	no ein._backers.b
	ein._funded = False
	ein._balance = 0
	max_block >= 0
	goal >= 0
	timeElapsed > 0

	//Post
	eout._owner = owner
	eout._maxBlock = max_block
	eout._goal = goal

	//out._owner = Address0x0
	//eout._maxBlock = 0
	//eout._goal = 0
	eout._backers = ein._backers
	eout._funded = False
	eout._balance = ein._balance
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	//eout._blockNumber = ein._blockNumber
}


pred pre_donate[e: EstadoConcreto] {
	e._maxBlock > e._blockNumber
}

pred met_donate [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int, timeElapsed: Int] {
	//PRE
	pre_donate [ein]
	(sender !in ein._backers.b.Int or ein._backers.b[sender] = 0)
	value >= 0
	value <= LIMIT[] //por la limitación de la sumatoria
	timeElapsed > 0

	//POST
	//(backers[sender] = 0) {
	eout._backers.b = ein._backers.b++sender->value
	eout._balance = ein._balance.add[value]

	eout._owner = ein._owner
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	//eout._backers = ein._backers
	//eout._sumaseq = ein.sumaseq
	eout._funded = ein._funded
	//eout._balance = ein._balance
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	//eout._blockNumber = ein._blockNumber
}


pred pre_getFunds [e: EstadoConcreto] {
	e._maxBlock < e._blockNumber
	e._goal <= e._balance
}

pred met_getFunds [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int, timeElapsed: Int] {
	//PRE
	pre_getFunds[ein]
	sender = ein._owner
	timeElapsed > 0

	//POST
	eout._funded = True
	eout._balance = 0

	eout._owner = ein._owner
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	eout._backers = ein._backers
	//eout._funded = ein._funded
	//eout._balance = ein._balance
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	//eout._blockNumber = ein._blockNumber
}

pred pre_claim[e: EstadoConcreto] {
	e._blockNumber > e._maxBlock
	e._funded = False
	e._goal > e._balance
	some a:Address | e._backers.b[a] > 0
}

pred met_claim[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int, timeElapsed: Int] {
	//PRE
	pre_claim[ein]
	ein._backers.b[sender] != 0
	timeElapsed > 0

	//POST
	(let val = ein._backers.b[sender] |
		eout._backers.b = ein._backers.b++sender->0 and 
		eout._balance = ein._balance.sub[val])

	eout._owner = ein._owner
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	//eout._backers = ein._backers
	//eout._sumaseq = ein._sumaseq
	eout._funded = ein._funded
	//eout._balance = ein._balance
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	//eout._blockNumber = ein._blockNumber
}


pred pre_t[e:EstadoConcreto] {
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int, timeElapsed: Int] {
	//PRE
	timeElapsed >= 0
	
	eout._owner = ein._owner
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	eout._backers = ein._backers
	eout._funded = ein._funded
	eout._balance = ein._balance
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
}



//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{
	(invariante[e])
	e._owner = Address0x0
	e._maxBlock = 0
	e._goal = 0
	no e._backers.b
	e._funded = False
	e._balance = 0
}



pred partitionINV[e: EstadoConcreto]{
	notInvariante[e]
}

pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and pre_getFunds[e] and pre_claim[e] and pre_t[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and pre_getFunds[e] and not pre_claim[e] and pre_t[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and pre_getFunds[e] and pre_claim[e] and not pre_t[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and pre_getFunds[e] and pre_claim[e] and pre_t[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and not pre_getFunds[e] and pre_claim[e] and pre_t[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and pre_getFunds[e] and not pre_claim[e] and pre_t[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and pre_getFunds[e] and not pre_claim[e] and not pre_t[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and pre_getFunds[e] and pre_claim[e] and not pre_t[e]
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and not pre_getFunds[e] and pre_claim[e] and not pre_t[e]
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and not pre_getFunds[e] and not pre_claim[e] and pre_t[e]
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and not pre_getFunds[e] and pre_claim[e] and pre_t[e]
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and not pre_getFunds[e] and not pre_claim[e] and pre_t[e]
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and pre_getFunds[e] and not pre_claim[e] and not pre_t[e]
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and not pre_getFunds[e] and pre_claim[e] and not pre_t[e]
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	pre_donate[e] and not pre_getFunds[e] and not pre_claim[e] and not pre_t[e]
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	not pre_donate[e] and not pre_getFunds[e] and not pre_claim[e] and not pre_t[e]
}

pred transicion_S00_a_S01_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S02_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S03_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S04_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S05_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S06_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S07_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S08_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S09_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S10_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S11_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S12_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S13_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S14_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S15_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

pred transicion_S00_a_S16_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21, v22, v23])
}

run transicion_S00_a_S01_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S04_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S05_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S06_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S07_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S08_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S09_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S10_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S11_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S12_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S13_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S14_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S15_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S00_a_S16_mediante_met_constructor  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S09_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S10_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S11_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S12_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S13_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S14_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S15_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S16_mediante_met_donate {
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S09_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S10_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S11_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S12_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S13_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S14_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S15_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S16_mediante_met_donate {
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S09_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S10_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S11_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S12_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S13_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S14_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S15_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S16_mediante_met_donate {
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S09_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S10_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S11_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S12_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S13_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S14_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S15_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S16_mediante_met_donate {
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S09_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S10_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S11_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S12_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S13_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S14_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S15_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S16_mediante_met_donate {
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S09_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S10_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S11_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S12_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S13_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S14_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S15_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S16_mediante_met_donate {
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S09_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S10_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S11_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S12_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S13_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S14_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S15_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S16_mediante_met_donate {
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S09_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S10_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S11_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S12_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S13_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S14_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S15_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S16_mediante_met_donate {
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S01_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S02_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S03_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S04_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S05_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S06_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S07_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S08_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S09_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S10_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S11_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S12_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S13_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S14_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S15_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S16_mediante_met_donate {
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S01_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S02_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S03_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S04_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S05_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S06_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S07_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S08_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S09_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S10_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S11_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S12_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S13_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S14_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S15_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S16_mediante_met_donate {
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S01_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S02_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S03_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S04_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S05_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S06_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S07_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S08_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S09_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S10_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S11_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S12_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S13_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S14_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S15_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S16_mediante_met_donate {
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S01_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S02_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S03_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S04_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S05_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S06_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S07_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S08_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S09_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S10_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S11_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S12_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S13_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S14_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S15_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S16_mediante_met_donate {
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S01_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S02_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S03_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S04_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S05_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S06_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S07_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S08_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S09_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S10_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S11_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S12_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S13_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S14_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S15_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S16_mediante_met_donate {
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S01_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S02_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S03_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S04_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S05_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S06_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S07_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S08_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S09_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S10_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S11_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S12_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S13_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S14_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S15_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S16_mediante_met_donate {
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S01_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S02_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S03_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S04_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S05_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S06_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S07_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S08_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S09_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S10_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S11_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S12_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S13_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S14_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S15_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S16_mediante_met_donate {
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S01_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S02_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S03_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S04_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S05_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S06_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S07_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S08_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S09_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S10_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S11_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S12_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S13_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S14_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S15_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S16_mediante_met_donate {
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_donate  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S01_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S02_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S03_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S04_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S05_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S06_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S07_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S08_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S09_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S10_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S11_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S12_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S13_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S14_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S15_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S16_mediante_met_donate  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S09_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S10_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S11_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S12_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S13_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S14_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S15_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S16_mediante_met_getFunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S09_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S10_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S11_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S12_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S13_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S14_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S15_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S16_mediante_met_getFunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S09_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S10_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S11_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S12_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S13_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S14_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S15_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S16_mediante_met_getFunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S09_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S10_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S11_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S12_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S13_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S14_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S15_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S16_mediante_met_getFunds {
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S09_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S10_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S11_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S12_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S13_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S14_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S15_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S16_mediante_met_getFunds {
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S09_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S10_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S11_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S12_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S13_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S14_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S15_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S16_mediante_met_getFunds {
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S09_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S10_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S11_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S12_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S13_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S14_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S15_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S16_mediante_met_getFunds {
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S09_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S10_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S11_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S12_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S13_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S14_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S15_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S16_mediante_met_getFunds {
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S01_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S02_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S03_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S04_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S05_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S06_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S07_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S08_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S09_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S10_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S11_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S12_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S13_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S14_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S15_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S16_mediante_met_getFunds {
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S01_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S02_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S03_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S04_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S05_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S06_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S07_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S08_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S09_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S10_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S11_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S12_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S13_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S14_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S15_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S16_mediante_met_getFunds {
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S01_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S02_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S03_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S04_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S05_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S06_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S07_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S08_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S09_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S10_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S11_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S12_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S13_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S14_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S15_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S16_mediante_met_getFunds {
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S01_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S02_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S03_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S04_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S05_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S06_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S07_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S08_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S09_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S10_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S11_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S12_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S13_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S14_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S15_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S16_mediante_met_getFunds {
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S01_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S02_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S03_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S04_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S05_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S06_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S07_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S08_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S09_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S10_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S11_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S12_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S13_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S14_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S15_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S16_mediante_met_getFunds {
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S01_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S02_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S03_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S04_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S05_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S06_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S07_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S08_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S09_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S10_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S11_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S12_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S13_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S14_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S15_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S16_mediante_met_getFunds {
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S01_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S02_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S03_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S04_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S05_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S06_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S07_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S08_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S09_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S10_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S11_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S12_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S13_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S14_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S15_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S16_mediante_met_getFunds {
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S01_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S02_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S03_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S04_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S05_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S06_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S07_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S08_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S09_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S10_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S11_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S12_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S13_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S14_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S15_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S16_mediante_met_getFunds {
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_getFunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S01_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S02_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S03_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S04_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S05_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S06_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S07_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S08_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S09_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S10_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S11_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S12_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S13_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S14_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S15_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S16_mediante_met_getFunds  for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S09_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S10_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S11_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S12_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S13_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S14_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S15_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S16_mediante_met_claim{
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S09_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S10_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S11_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S12_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S13_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S14_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S15_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S16_mediante_met_claim{
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S09_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S10_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S11_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S12_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S13_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S14_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S15_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S16_mediante_met_claim{
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S09_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S10_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S11_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S12_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S13_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S14_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S15_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S16_mediante_met_claim{
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S09_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S10_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S11_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S12_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S13_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S14_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S15_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S16_mediante_met_claim{
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S09_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S10_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S11_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S12_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S13_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S14_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S15_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S16_mediante_met_claim{
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S09_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S10_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S11_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S12_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S13_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S14_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S15_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S16_mediante_met_claim{
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S09_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S10_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S11_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S12_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S13_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S14_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S15_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S16_mediante_met_claim{
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S01_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S02_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S03_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S04_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S05_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S06_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S07_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S08_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S09_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S10_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S11_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S12_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S13_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S14_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S15_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S16_mediante_met_claim{
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S01_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S02_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S03_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S04_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S05_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S06_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S07_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S08_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S09_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S10_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S11_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S12_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S13_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S14_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S15_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S16_mediante_met_claim{
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S01_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S02_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S03_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S04_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S05_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S06_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S07_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S08_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S09_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S10_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S11_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S12_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S13_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S14_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S15_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S16_mediante_met_claim{
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S01_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S02_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S03_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S04_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S05_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S06_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S07_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S08_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S09_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S10_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S11_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S12_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S13_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S14_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S15_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S16_mediante_met_claim{
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S01_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S02_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S03_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S04_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S05_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S06_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S07_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S08_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S09_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S10_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S11_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S12_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S13_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S14_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S15_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S16_mediante_met_claim{
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S01_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S02_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S03_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S04_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S05_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S06_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S07_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S08_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S09_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S10_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S11_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S12_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S13_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S14_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S15_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S16_mediante_met_claim{
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S01_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S02_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S03_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S04_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S05_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S06_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S07_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S08_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S09_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S10_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S11_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S12_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S13_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S14_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S15_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S16_mediante_met_claim{
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S01_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S02_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S03_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S04_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S05_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S06_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S07_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S08_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S09_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S10_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S11_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S12_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S13_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S14_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S15_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S16_mediante_met_claim{
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_claim [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S01_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S02_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S03_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S04_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S05_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S06_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S07_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S08_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S09_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S10_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S11_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S12_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S13_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S14_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S15_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S16_mediante_met_claim for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S09_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S10_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S11_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S12_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S13_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S14_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S15_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S16_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S09_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S10_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S11_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S12_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S13_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S14_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S15_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S16_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S09_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S10_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S11_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S12_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S13_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S14_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S15_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S16_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S09_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S10_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S11_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S12_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S13_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S14_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S15_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S16_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S09_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S10_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S11_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S12_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S13_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S14_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S15_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S16_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S09_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S10_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S11_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S12_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S13_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S14_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S15_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S16_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S09_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S10_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S11_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S12_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S13_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S14_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S15_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S16_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S09_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S10_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S11_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S12_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S13_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S14_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S15_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S16_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S01_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S02_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S03_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S04_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S05_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S06_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S07_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S08_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S09_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S10_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S11_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S12_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S13_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S14_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S15_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S16_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S01_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S02_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S03_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S04_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S05_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S06_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S07_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S08_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S09_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S10_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S11_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S12_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S13_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S14_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S15_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S16_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S01_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S02_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S03_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S04_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S05_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S06_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S07_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S08_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S09_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S10_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S11_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S12_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S13_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S14_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S15_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S16_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S01_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S02_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S03_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S04_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S05_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S06_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S07_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S08_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S09_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S10_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S11_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S12_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S13_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S14_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S15_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S16_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S01_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S02_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S03_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S04_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S05_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S06_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S07_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S08_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S09_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S10_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S11_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S12_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S13_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S14_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S15_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S16_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S01_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S02_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S03_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S04_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S05_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S06_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S07_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S08_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S09_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S10_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S11_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S12_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S13_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S14_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S15_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S16_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S01_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S02_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S03_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S04_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S05_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S06_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S07_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S08_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S09_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S10_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S11_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S12_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S13_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S14_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S15_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S16_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S01_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S02_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S03_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S04_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S05_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S06_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S07_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S08_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S09_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S10_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S11_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S12_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S13_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S14_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S15_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S16_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S01_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S02_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S03_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S04_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S05_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S06_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S07_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S08_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S09_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S10_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S11_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S12_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S13_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S14_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S15_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S08_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S09_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S10_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S11_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S12_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S13_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S14_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S15_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
run transicion_S16_a_S16_mediante_met_t for 2 EstadoConcreto, 2 Backer, 2 SumatoriaSeq
