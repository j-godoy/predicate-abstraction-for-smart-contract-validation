// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


// estados concretos
abstract sig Address{name: Name}
one sig Address0 extends Address{}
one sig Address1 extends Address{}
one sig Address2 extends Address{}
one sig Address3 extends Address{}
one sig Address4 extends Address{}
one sig Address5 extends Address{}

abstract sig Name{}
one sig NameA extends Name{}
one sig NameB extends Name{}
one sig NameC extends Name{}
one sig NameD extends Name{}
one sig NameE extends Name{}
one sig NameF extends Name{}

abstract sig EstadoContrato{}
one sig SetFlyerAndReward extends EstadoContrato{}
one sig MilesAdded extends EstadoContrato{}

sig Miles {s: seq Int }

abstract sig EstadoConcreto {
	_airlineRepresentative: lone Address,
	_flyer: lone Address,
	_rewardsPerMile: lone Int,
	_miles: lone Miles,
	_indexCalculatedUpto: lone Int,
	_totalRewards: lone Int,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	(no disj a1,a2:Address | a1.name = a2.name)
}


pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
				flyer: Address, rewardsPerMile: Int] {
	//Pre
	no ein._airlineRepresentative
	no ein._flyer
	no ein._rewardsPerMile
	no ein._miles
	no ein._indexCalculatedUpto
	no ein._totalRewards
	no ein._state
	//Post
	eout._airlineRepresentative = sender
	eout._flyer = flyer
	eout._rewardsPerMile = rewardsPerMile
	eout._indexCalculatedUpto = 0
	eout._totalRewards = 0
	eout._state = SetFlyerAndReward

	#eout._miles.s = 0

	//eout._airlineRepresentative = ein._airlineRepresentative
	//eout._flyer = ein._flyer
	//eout._rewardsPerMile = ein._rewardsPerMile
	//eout._miles = ein._miles
	//eout._indexCalculatedUpto = ein._indexCalculatedUpto
	//eout._totalRewards = ein._totalRewards
	//eout._state = ein._state
}

pred met_addMiles[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, miles: Miles] {
	//Pre
	some ein._state
	ein._flyer = sender
	
	//Post
	agregarMiles[ein, eout, miles]
	//computeTotalRewards(ein,eout)
	eout._state = MilesAdded

	//eout._airlineRepresentative = ein._airlineRepresentative
	//eout._flyer = ein._flyer
	//eout._rewardsPerMile = ein._rewardsPerMile
	//eout._miles = ein._miles
	//eout._indexCalculatedUpto = ein._indexCalculatedUpto
	//eout._totalRewards = ein._totalRewards
	//eout._state = ein._state
}

pred agregarMiles[ein: EstadoConcreto, eout: EstadoConcreto, miles: Miles] {
	#eout._miles.s = (#ein._miles.s).add[#miles.s]
	all x: Int | x>= 0 and x <= #ein._miles.s implies ein._miles.s[x] in eout._miles.s.elems
	all x: Int | x>= 0 and x <= #miles.s implies miles.s[x] in eout._miles.s.elems
}

pred met_getMiles[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre	
	some ein._state
	//Post
	eout = ein
}


// agrego un predicado por cada partición teórica posible
pred particionS00[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._state
}

pred particionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SetFlyerAndReward
}

pred particionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = MilesAdded
}

pred particionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}

// agregar un predicado para cada transición posible
/*
De S0 a SN con acción
*/
pred transicion_S00_a_S00_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S01_a_INV_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

pred transicion_S02_a_INV_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20])
}

run transicion_S00_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address, 3 Miles
pred transicion_S00_a_S00_mediante_met_addMiles{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_addMiles{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_addMiles{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_addMiles{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_addMiles{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_addMiles{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_addMiles{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_addMiles{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_addMiles{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_addMiles{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_addMiles{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_addMiles{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Miles | met_addMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_S01_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_S02_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_INV_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S00_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S01_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S02_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_INV_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S00_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S01_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S02_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_INV_mediante_met_addMiles for 2 EstadoConcreto, 5 Address, 3 Miles
pred transicion_S00_a_S00_mediante_met_getMiles{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_getMiles{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_getMiles{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_getMiles{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_getMiles{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_getMiles{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_getMiles{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_getMiles{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_getMiles{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_getMiles{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_getMiles{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_getMiles{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_getMiles [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_S01_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_S02_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S00_a_INV_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S00_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S01_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_S02_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S01_a_INV_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S00_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S01_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_S02_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
run transicion_S02_a_INV_mediante_met_getMiles for 2 EstadoConcreto, 5 Address, 3 Miles
