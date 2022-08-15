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

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}

sig Deposit{d: Address->Int}

// estados concretos
abstract sig EstadoConcreto {
	_beneficiary: Address,
	_deposits: Deposit,
	_owner: Address,
	_balance: Int,
	_blockNumber: Int, //lo agrego para simular el paso del tiempo
	_state: lone State
}

abstract sig State{}
one sig Active extends State {}
one sig Refunding extends State{}
one sig Closed extends State{}

fun LIMIT[]: Int {3}


//run transicion_S03_a_INV_mediante_met_beneficiaryWithdraw for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq

pred invariante [e:EstadoConcreto] {
	//En estado Active, la suma de depósitos debe ser igual al balance
	(e._state = Active) implies sumatoria[e._deposits, e._balance]

	//Si se terminó el tiempo, debe suceder que balance < sumaDepósitos
	//Más especificamente, balance debe ser igual sumatoria de sumaDepósitos para k elementos (0<=k<#deposits)
	e._state = Closed implies (e._balance=0 or sumatoriaSubSeq[e._deposits, e._balance])

	e._state = Refunding implies sumatoriaSubSeq[e._deposits, e._balance]

	//No Negativos
	e._balance >= 0 and e._blockNumber >= 0
	all d0:Address | e._deposits.d[d0] >= 0

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._deposits.d[d0] >= 0 and e._deposits.d[d0] <= LIMIT[]
	#(e._deposits.d.Int) <= 4
}

pred notInvariante[e: EstadoConcreto]{
	(not invariante[e])
	some sumaSeq: SumatoriaSeq, suma: Int | toSeq[e._deposits, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
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

pred sumatoria [s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}

pred sumatoriaSubSeq [s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
}

pred subSeq [original: seq Int, subseq: seq Int] {
	#subseq <= #original
	all i: Int | some subseq[i] implies subseq[i] in original.elems
	all i: Int | some subseq[i] implies #subseq.i <= #original.i
}

pred toSeq [s: set Deposit, ret: seq Int] {
	all d0: s.d.Int | some i: Int | ret[i]=s.d[d0] //Todo elemento del set está en la seq
	all i: Int | some ret[i] implies some d0: s.d.Int | s.d[d0]=ret[i]//Todo elemento de la seq está en el set
	all i: Int | #(s.d.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
	#(s.d.Int)=#(ret)
}

sig SumatoriaSeq {sec: seq Int}

pred met_constructor [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, beneficiary: Address, timeElapsed: Int] {
	//Pre
	ein._beneficiary = Address0x0
	ein._owner = Address0x0
	ein._balance = 0
	no ein._state
	beneficiary != Address0x0
	sender != Address0x0
	timeElapsed > 0


	//Post
	eout._beneficiary = beneficiary
	eout._owner = sender
	eout._state = Active

	eout._deposits = ein._deposits
	//eout._beneficiary = ein._beneficiary
	//eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._balance = ein._balance
}


pred pre_deposit [ein: EstadoConcreto] {
	ein._state = Active
}

pred met_deposit [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, refundee: Address, value: Int, timeElapsed: Int] {
	//PRE
	pre_deposit [ein]
	ein._owner = sender
	timeElapsed > 0
	value >= 0
	value <= LIMIT[] //por la limitación de la sumatoria
	ein._deposits.d[refundee].add[value] <= LIMIT[]
	
	//POST
	eout._deposits.d = ein._deposits.d++refundee->ein._deposits.d[refundee].add[value]
	eout._balance = ein._balance.add[value]

	//eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	//eout._balance = ein._balance
}


pred pre_close [ein: EstadoConcreto] {
	ein._state = Active
}

pred met_close [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, refundee: Address, value: Int, timeElapsed: Int] {
	//PRE
	pre_close [ein]
	ein._owner = sender
	timeElapsed > 0
	
	//POST
	eout._state = Closed

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._balance = ein._balance
}



pred pre_enableRefunds [ein: EstadoConcreto] {
	ein._state = Active
}

pred met_enableRefunds [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, timeElapsed: Int] {
	//PRE
	pre_enableRefunds [ein]
	ein._owner = sender
	timeElapsed > 0
	
	//POST
	eout._state = Refunding

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._balance = ein._balance
}



pred pre_beneficiaryWithdraw [ein: EstadoConcreto] {
	ein._state = Closed
	ein._balance > 0
}

pred met_beneficiaryWithdraw [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, timeElapsed: Int] {
	//PRE
	pre_beneficiaryWithdraw [ein]
	timeElapsed > 0
	
	//POST
	eout._balance = 0

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	//eout._balance = ein._balance
}


pred pre_withdraw [ein: EstadoConcreto] {
	ein._state = Refunding
}

pred met_withdraw [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, payee: Address, timeElapsed: Int] {
	//PRE
	pre_withdraw [ein]
	ein._deposits.d[payee] > 0
	timeElapsed > 0
	
	//POST
	eout._deposits.d = ein._deposits.d++payee->0
	eout._balance = ein._balance.sub[ein._deposits.d[payee]]

	//eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	//eout._balance = ein._balance
}





pred pre_transferPrimary [e: EstadoConcreto] {
	some e._state
	e._owner != Address0x0
}

pred met_transferPrimary [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, recipient: Address, timeElapsed: Int] {
	///PRE
	pre_transferPrimary[ein]
	ein._owner = sender
	recipient != Address0x0
	timeElapsed > 0

	//POST
	eout._owner = recipient

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	//eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._balance = ein._balance
}




//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////

pred partitionS00[e: EstadoConcreto]{
	(invariante[e])
	e._owner = Address0x0
	no e._state
	no e._deposits.d
}

pred partitionINV[e: EstadoConcreto]{
	notInvariante[e]
}

pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	e._state = Active
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	e._state = Refunding
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	e._state = Closed
}




pred transicion_S00_a_S00_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S01_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S02_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S03_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_INV_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S00_mediante_met_constructor {
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S01_mediante_met_constructor {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S02_mediante_met_constructor {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S03_mediante_met_constructor {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_INV_mediante_met_constructor {
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S00_mediante_met_constructor {
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S01_mediante_met_constructor {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S02_mediante_met_constructor {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S03_mediante_met_constructor {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_INV_mediante_met_constructor {
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S00_mediante_met_constructor {
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S01_mediante_met_constructor {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S02_mediante_met_constructor {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S03_mediante_met_constructor {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_INV_mediante_met_constructor {
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

run transicion_S00_a_S00_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S01_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S00_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S01_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S00_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S00_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S00_a_S00_mediante_met_deposit {
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_deposit {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_deposit {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_deposit {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_INV_mediante_met_deposit {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_deposit {
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_deposit {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_deposit {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_deposit {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_deposit {
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_deposit {
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_deposit {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_deposit {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_deposit {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_deposit {
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_deposit {
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_deposit {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_deposit {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_deposit {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_deposit {
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_deposit  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

run transicion_S00_a_S00_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S01_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S00_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S01_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S00_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S00_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_deposit  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S00_a_S00_mediante_met_close {
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_close {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_close {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_close {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_INV_mediante_met_close {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_close {
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_close {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_close {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_close {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_close {
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_close {
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_close {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_close {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_close {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_close {
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_close {
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_close {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_close {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_close {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_close {
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_close  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

run transicion_S00_a_S00_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S01_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S00_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S01_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S00_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S00_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_close  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S00_a_S00_mediante_met_enableRefunds {
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_enableRefunds {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_enableRefunds {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_enableRefunds {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_enableRefunds {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_enableRefunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_enableRefunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_enableRefunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_enableRefunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_enableRefunds {
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_enableRefunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_enableRefunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_enableRefunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_enableRefunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_enableRefunds {
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_enableRefunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_enableRefunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_enableRefunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_enableRefunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_enableRefunds {
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_enableRefunds  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S01_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S00_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S01_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S00_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S00_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_enableRefunds  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S00_a_S00_mediante_met_beneficiaryWithdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_beneficiaryWithdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_beneficiaryWithdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_beneficiaryWithdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_beneficiaryWithdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_beneficiaryWithdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_beneficiaryWithdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_beneficiaryWithdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_beneficiaryWithdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_beneficiaryWithdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_beneficiaryWithdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_beneficiaryWithdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_beneficiaryWithdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_beneficiaryWithdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_beneficiaryWithdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_beneficiaryWithdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_beneficiaryWithdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_beneficiaryWithdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_beneficiaryWithdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_beneficiaryWithdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_beneficiaryWithdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S01_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S00_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S01_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S00_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S00_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_beneficiaryWithdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S00_a_S00_mediante_met_withdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S01_mediante_met_withdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S02_mediante_met_withdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S03_mediante_met_withdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_INV_mediante_met_withdraw {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S00_mediante_met_withdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S01_mediante_met_withdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S02_mediante_met_withdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S03_mediante_met_withdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_INV_mediante_met_withdraw {
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S00_mediante_met_withdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S01_mediante_met_withdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S02_mediante_met_withdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S03_mediante_met_withdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_INV_mediante_met_withdraw {
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S00_mediante_met_withdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S01_mediante_met_withdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S02_mediante_met_withdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S03_mediante_met_withdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_INV_mediante_met_withdraw {
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_withdraw  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

run transicion_S00_a_S00_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S01_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S00_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S01_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S00_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S00_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_withdraw  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S00_a_S00_mediante_met_transferPrimary {
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S01_mediante_met_transferPrimary {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S02_mediante_met_transferPrimary {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S03_mediante_met_transferPrimary {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_INV_mediante_met_transferPrimary {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S00_mediante_met_transferPrimary {
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S01_mediante_met_transferPrimary {
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S02_mediante_met_transferPrimary {
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S03_mediante_met_transferPrimary {
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_INV_mediante_met_transferPrimary {
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S00_mediante_met_transferPrimary {
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S01_mediante_met_transferPrimary {
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S02_mediante_met_transferPrimary {
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S03_mediante_met_transferPrimary {
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_INV_mediante_met_transferPrimary {
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S00_mediante_met_transferPrimary {
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S01_mediante_met_transferPrimary {
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S02_mediante_met_transferPrimary {
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_S03_mediante_met_transferPrimary {
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S03_a_INV_mediante_met_transferPrimary {
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_transferPrimary  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

run transicion_S00_a_S00_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S01_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S00_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S01_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S00_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S00_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_transferPrimary  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
