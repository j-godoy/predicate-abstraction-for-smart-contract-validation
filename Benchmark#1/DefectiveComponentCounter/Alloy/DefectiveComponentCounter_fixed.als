// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


// estados concretos
abstract sig Address{}
one sig Address0 extends Address{}
one sig Address1 extends Address{}
one sig Address2 extends Address{}
one sig Address3 extends Address{}
one sig Address4 extends Address{}
one sig Address5 extends Address{}

abstract sig EstadoContrato{}
one sig Create extends EstadoContrato{}
one sig ComputeTotal extends EstadoContrato{}

one sig Secuencia{s1:seq Int} {s1[0]=1 and s1[1]=2 and s1[2]=3 and #s1=3}

abstract sig EstadoConcreto {
	_manufacturer: lone Address,
	_defectiveComponentsCount: Secuencia,
	_total: lone Int,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	//(no disj a1,a2:Address | a1.name = a2.name)
}


pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, defectiveComponentsCount: Secuencia] {
	//Pre
	(no ein._manufacturer and no ein._total and no ein._state)
	//Post
	eout._manufacturer = sender
	eout._defectiveComponentsCount = defectiveComponentsCount
	eout._total = 0
	eout._state = Create

	//eout._manufacturer = ein._manufacturer
	//eout._defectiveComponentsCount = ein._defectiveComponentsCount
	//eout._total = ein._total
	//eout._state = ein._state
}

pred met_computeTotal[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._manufacturer = sender
	ein._state != ComputeTotal
	//Post

        // calculate total for only the first 12 values, in case more than 12 are entered
	eout._total = allsum[ein._defectiveComponentsCount.s1.elems]
	eout._state = ComputeTotal
	
	eout._manufacturer = ein._manufacturer
	eout._defectiveComponentsCount = ein._defectiveComponentsCount
	//eout._total = ein._total
	//eout._state = ein._state
}

// Tiene el problema de que no suma repetidos.
fun allsum[defectiveComponentsCount: set Int] : Int {
    sum s: defectiveComponentsCount | s
}

pred met_getDefectiveComponentsCount[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
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
	e._state = Create
}

pred particionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = ComputeTotal
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
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Secuencia | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_computeTotal{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_computeTotal{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_computeTotal{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_computeTotal{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_computeTotal{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_computeTotal{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_computeTotal{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_computeTotal{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_computeTotal{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_computeTotal{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_computeTotal{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_computeTotal{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_computeTotal [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_computeTotal for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_getDefectiveComponentsCount{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_getDefectiveComponentsCount{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_getDefectiveComponentsCount{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_getDefectiveComponentsCount{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_getDefectiveComponentsCount{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_getDefectiveComponentsCount{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_getDefectiveComponentsCount{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_getDefectiveComponentsCount{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_getDefectiveComponentsCount{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_getDefectiveComponentsCount{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_getDefectiveComponentsCount{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_getDefectiveComponentsCount{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_getDefectiveComponentsCount [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_getDefectiveComponentsCount for 2 EstadoConcreto, 5 Address
