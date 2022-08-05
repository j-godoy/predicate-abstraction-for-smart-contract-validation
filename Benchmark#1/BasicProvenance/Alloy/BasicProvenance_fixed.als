// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{transiciones: Accion -> set EstadoAbstracto}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


//Acciones de los estados abstractos
abstract sig Accion{}
one sig AccionConstructor extends Accion {}
one sig AccionTransferResponsibility extends Accion {}
one sig AccionComplete extends Accion {}
one sig AccionTransferResponsibilityNotAssert extends Accion {}
one sig AccionCompleteNotAssert extends Accion {}

// Describo cómo pasar de un estado a otro mediante cada acción
fact trans_accionConstructor{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionConstructor]
				iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal, d1,d2,d3:Address | constructor[e0,e1, d1, d2, d3] and
				FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionTransferResponsibility{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionTransferResponsibility]
				iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal, d1,d2:Address | transferResponsibility[e0, e1, d1, d2] and
				FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionComplete{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionComplete]
			iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal, d1:Address | complete[e0,e1,d1] and
			FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1)}

/*fact trans_accionTransferResponsibility{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionTransferResponsibilityNotAssert]
				iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal, d1,d2:Address | transferResponsibilityNotAssert[e0, e1, d1, d2] and
				FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionComplete{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionCompleteNotAssert]
			iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal, d1:Address | completeNotAssert[e0,e1,d1] and
			FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1)}*/


// Declaro fn de abstracción que relaciona estado concreto con estado abstracto
one sig FnAbstraccion{F: EstadoConcreto -> one EstadoAbstracto}

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
one sig Created extends EstadoContrato{}
one sig InTransit extends EstadoContrato{}
one sig Completed extends EstadoContrato{}

abstract sig EstadoConcreto {
	_initiatingCounterparty: one Address,
	_counterparty: one Address,
	_previousCounterparty: one Address,
	_supplyChainOwner: one Address,
	_supplyChainObserver: one Address,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	(no disj a1,a2:Address | a1.name = a2.name)
}


pred constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, supplyChainOwner:Address, supplyChainObserver:Address] {
	//Pre
	no ein._state
        eout._initiatingCounterparty = sender
        eout._counterparty = eout._initiatingCounterparty
        eout._supplyChainOwner = supplyChainOwner
        eout._supplyChainObserver = supplyChainObserver
        eout._state = Created
}

pred transferResponsibility[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, newCounterparty: Address]{
	//Pre	
	some ein._state and ein._counterparty = sender and ein._state != Completed
	//ein._state = Created or ein._state = InTransit // agregan assert
	//Post
	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = newCounterparty
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
        ein._state = Created => eout._state = InTransit else eout._state = ein._state
}

/*pred transferResponsibilityNotAssert[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, newCounterparty: Address]{
	//Pre	
	some ein._state and ein._counterparty = sender and ein._state != Completed
	not (ein._state = Created or ein._state = InTransit)
	//Post
	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = newCounterparty
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
        ein._state = Created => eout._state = InTransit else eout._state = ein._state
}*/

pred complete[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address]{
	//Pre	
	some ein._state and ein._supplyChainOwner = sender and ein._state != Completed and ein._state != Created
	//Post
	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = Address0
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
        eout._state = Completed
}

/*pred completeNotAssert[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address]{
	//Pre	
	some ein._state and ein._supplyChainOwner = sender and ein._state != Completed
	not(ein._state = InTransit)
	not(ein._state = Created)
	//Post
	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = Address0
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
        eout._state = Completed
}*/


// agrego un predicado por cada partición teórica posible
pred particionS0[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._state
}

pred particionS1[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Created
}

pred particionS2[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = InTransit
}

pred particionS3[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Completed
}

pred particionIN[e: EstadoConcreto]{ // 
	not (invariante[e])
}

// agregar un predicado para cada transición posible
/*
De S0 a SN con acción
*/
pred transicion_S0_a_S0_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S0_a_S1_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S0_a_S2_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S0_a_S3_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S0_a_IN_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S1_a_S1_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S1_a_S0_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S1_a_S2_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S1_a_S3_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S1_a_IN_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S2_a_S2_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S2_a_S0_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S2_a_S1_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S2_a_S3_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S2_a_IN_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S3_a_S3_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS3[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S3_a_S0_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S3_a_S1_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S3_a_S2_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S3_a_IN_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


run transicion_S0_a_S0_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S1_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S2_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S3_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_IN_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S1_a_S1_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S0_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S2_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S3_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_IN_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S2_a_S2_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S0_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S1_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S3_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_IN_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S3_a_S3_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S0_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S1_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S2_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_IN_mediante_constructor for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

pred transicion_S0_a_S0_mediante_transferResponsibility{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S0_a_S1_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S0_a_S2_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S0_a_S3_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S0_a_IN_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}


pred transicion_S1_a_S1_mediante_transferResponsibility{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S1_a_S0_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S1_a_S2_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S1_a_S3_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S1_a_IN_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}


pred transicion_S2_a_S2_mediante_transferResponsibility{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S2_a_S0_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S2_a_S1_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S2_a_S3_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S2_a_IN_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}


pred transicion_S3_a_S3_mediante_transferResponsibility{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS3[e]))
	(A0 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S3_a_S0_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S3_a_S1_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S3_a_S2_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S3_a_IN_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}


run transicion_S0_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S1_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S2_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S3_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

pred transicion_S0_a_S0_mediante_complete{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionComplete])
}

pred transicion_S0_a_S1_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S0_a_S2_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S0_a_S3_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S0_a_IN_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}


pred transicion_S1_a_S1_mediante_complete{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionComplete])
}

pred transicion_S1_a_S0_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S1_a_S2_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S1_a_S3_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S1_a_IN_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}


pred transicion_S2_a_S2_mediante_complete{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionComplete])
}

pred transicion_S2_a_S0_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S2_a_S1_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S2_a_S3_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S2_a_IN_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}


pred transicion_S3_a_S3_mediante_complete{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS3[e]))
	(A0 in A0.transiciones[AccionComplete])
}

pred transicion_S3_a_S0_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S3_a_S1_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S3_a_S2_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S3_a_IN_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}


run transicion_S0_a_S0_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S1_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S2_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_S3_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S0_a_IN_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S1_a_S1_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S0_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S2_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_S3_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S1_a_IN_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S2_a_S2_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S0_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S1_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_S3_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S2_a_IN_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address

run transicion_S3_a_S3_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S0_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S1_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_S2_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
run transicion_S3_a_IN_mediante_complete for 2 EstadoConcreto, 2 EstadoConcreto, 7 Address
