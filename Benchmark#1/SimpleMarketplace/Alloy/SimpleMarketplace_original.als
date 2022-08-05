// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{transiciones: Accion -> set EstadoAbstracto}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


//Acciones de los estados abstractos
abstract sig Accion{}
one sig AccionConstructor extends Accion {}
one sig AccionMakeOffer extends Accion {}
one sig AccionReject extends Accion {}
one sig AccionAcceptOffer extends Accion {}

// Describo cómo pasar de un estado a otro mediante cada acción
fact trans_accionConstructor{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionConstructor]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Texto,v30:Int | constructor[e0,e1,v10,v20,v30]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionMakeOffer{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionMakeOffer]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Int | makeOffer[e0,e1,v10,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionReject{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionReject]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | reject[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionAcceptOffer{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionAcceptOffer]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | acceptOffer[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

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

abstract sig Texto{}
one sig TextoA extends Texto{}
one sig TextoB extends Texto{}
one sig TextoC extends Texto{}
one sig TextoD extends Texto{}

abstract sig EstadoContrato{}
one sig ItemAvailable extends EstadoContrato{}
one sig OfferPlaced extends EstadoContrato{}
one sig Accepted extends EstadoContrato{}

abstract sig EstadoConcreto {
	_instanceOwner: lone Address,
	_instanceBuyer: lone Address,
	_description: lone Texto,
	_askingPrice: lone Int,
	_offerPrice: lone Int,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


//fact {all x: Int | x > 0}

pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	(no disj a1,a2:Address | a1.name = a2.name)
	no e._offerPrice or e._offerPrice > 0
	no e._askingPrice  or e._askingPrice > 0
}

pred constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, description: Texto, price: Int] {
	//Pre
	no ein._state and no ein._instanceBuyer and no ein._description and no ein._askingPrice
	and no ein._instanceOwner and no ein._offerPrice
	price > 0 // Esto lo agregué pero no está en el código
	//Post
	eout._instanceOwner = sender
	no eout._instanceBuyer
	eout._description = description
	eout._askingPrice = price
	no eout._offerPrice
	eout._state = ItemAvailable
}

pred makeOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, offerPrice: Int] {
	//Pre
	(some ein._state) and offerPrice > 0
	ein._state = ItemAvailable and ein._instanceOwner != sender
	//Post
	eout._instanceOwner = ein._instanceOwner
	eout._instanceBuyer = 	sender
	eout._description = ein._description
	eout._askingPrice = ein._askingPrice
	eout._offerPrice = offerPrice
	eout._state = OfferPlaced
}

pred reject[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state and ein._state = OfferPlaced and ein._instanceOwner = sender
	//Post
	eout._instanceOwner = ein._instanceOwner
	no eout._instanceBuyer
	eout._description = ein._description
	eout._askingPrice = ein._askingPrice
	eout._offerPrice = ein._offerPrice
	eout._state = ItemAvailable
}


pred acceptOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state and ein._instanceOwner = sender
	//Post
	eout._instanceOwner = ein._instanceOwner
	eout._instanceBuyer = ein._instanceBuyer
	eout._description = ein._description
	eout._askingPrice = ein._askingPrice
	eout._offerPrice = ein._offerPrice
	eout._state = Accepted
}


// agrego un predicado por cada partición teórica posible
pred particionS0[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._state
}

pred particionS1[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = ItemAvailable
}

pred particionS2[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = OfferPlaced
}

pred particionS3[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Accepted
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


run transicion_S0_a_S0_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S1_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S2_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S3_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_IN_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S1_a_S1_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S0_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S2_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S3_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_IN_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S2_a_S2_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S0_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S1_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S3_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_IN_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S3_a_S3_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S0_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S1_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S2_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_IN_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Texto

pred transicion_S0_a_S0_mediante_makeOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S0_a_S1_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S0_a_S2_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S0_a_S3_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S0_a_IN_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}


pred transicion_S1_a_S1_mediante_makeOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S1_a_S0_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S1_a_S2_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S1_a_S3_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S1_a_IN_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}


pred transicion_S2_a_S2_mediante_makeOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S2_a_S0_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S2_a_S1_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S2_a_S3_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S2_a_IN_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}


pred transicion_S3_a_S3_mediante_makeOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS3[e]))
	(A0 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S3_a_S0_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S3_a_S1_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S3_a_S2_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}

pred transicion_S3_a_IN_mediante_makeOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionMakeOffer])
}


run transicion_S0_a_S0_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S1_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S2_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S3_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_IN_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S1_a_S1_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S0_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S2_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S3_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_IN_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S2_a_S2_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S0_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S1_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S3_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_IN_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S3_a_S3_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S0_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S1_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S2_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_IN_mediante_makeOffer for 2 EstadoConcreto, 4 Address, 4 Texto

pred transicion_S0_a_S0_mediante_reject{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionReject])
}

pred transicion_S0_a_S1_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S0_a_S2_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S0_a_S3_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S0_a_IN_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}


pred transicion_S1_a_S1_mediante_reject{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionReject])
}

pred transicion_S1_a_S0_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S1_a_S2_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S1_a_S3_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S1_a_IN_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}


pred transicion_S2_a_S2_mediante_reject{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionReject])
}

pred transicion_S2_a_S0_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S2_a_S1_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S2_a_S3_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S2_a_IN_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}


pred transicion_S3_a_S3_mediante_reject{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS3[e]))
	(A0 in A0.transiciones[AccionReject])
}

pred transicion_S3_a_S0_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S3_a_S1_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S3_a_S2_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}

pred transicion_S3_a_IN_mediante_reject{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReject])
}


run transicion_S0_a_S0_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S1_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S2_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S3_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_IN_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S1_a_S1_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S0_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S2_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S3_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_IN_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S2_a_S2_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S0_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S1_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S3_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_IN_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S3_a_S3_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S0_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S1_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S2_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_IN_mediante_reject for 2 EstadoConcreto, 4 Address, 4 Texto

pred transicion_S0_a_S0_mediante_acceptOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S0_a_S1_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S0_a_S2_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S0_a_S3_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S0_a_IN_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}


pred transicion_S1_a_S1_mediante_acceptOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S1_a_S0_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S1_a_S2_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S1_a_S3_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S1_a_IN_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}


pred transicion_S2_a_S2_mediante_acceptOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S2_a_S0_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S2_a_S1_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S2_a_S3_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S2_a_IN_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}


pred transicion_S3_a_S3_mediante_acceptOffer{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS3[e]))
	(A0 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S3_a_S0_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S3_a_S1_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S3_a_S2_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}

pred transicion_S3_a_IN_mediante_acceptOffer{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptOffer])
}


run transicion_S0_a_S0_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S1_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S2_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_S3_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S0_a_IN_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S1_a_S1_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S0_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S2_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_S3_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S1_a_IN_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S2_a_S2_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S0_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S1_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_S3_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S2_a_IN_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto

run transicion_S3_a_S3_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S0_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S1_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_S2_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
run transicion_S3_a_IN_mediante_acceptOffer for 2 EstadoConcreto, 4 Address, 4 Texto
