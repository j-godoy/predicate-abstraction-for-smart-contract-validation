// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{transiciones: Accion -> set EstadoAbstracto}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


//Acciones de los estados abstractos
abstract sig Accion{}
one sig AccionConstructor extends Accion {}
one sig AccionSendRequest extends Accion {}
one sig AccionSendResponse extends Accion {}

// Describo cómo pasar de un estado a otro mediante cada acción
fact trans_accionConstructor{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionConstructor]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Message | constructor[e0,e1,v10,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionSendRequest{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionSendRequest]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Message | sendRequest[e0,e1,v10,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionSendResponse{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionSendResponse]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Message | sendResponse[e0,e1,v10,v20]
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

abstract sig Message{}
one sig MessageA extends Message{}
one sig MessageB extends Message{}
one sig MessageC extends Message{}
one sig MessageD extends Message{}

abstract sig EstadoContrato{}
one sig Request extends EstadoContrato{}
one sig Respond extends EstadoContrato{}

abstract sig EstadoConcreto {
	_requestor: one Address,
	_responder: one Address,
	_requestMessage: lone Message,
	_responseMessage: lone Message,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	(no disj a1,a2:Address | a1.name = a2.name)
}

pred constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, message: Message] {
	//Pre
	no ein._state
	//Post
	eout._requestor = sender
	eout._responder = ein._responder
        eout._requestMessage = message
	eout._responseMessage = ein._responseMessage
        eout._state = Request
}

pred sendRequest[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, requestMessage: Message] {
	//Pre
	(some ein._state) and ein._requestor = sender
	ein._state = Respond // agrego FIX
	//Post
	eout._requestMessage = requestMessage
	eout._state = Request
	eout._requestor = ein._requestor
	eout._responder = ein._responder
	eout._responseMessage = ein._responseMessage
}

pred sendResponse[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, responseMessage: Message] {
	//Pre
	some ein._state
	ein._state = Request // agrego FIX
	//Post
	eout._responseMessage = responseMessage
	eout._state = Respond
	eout._requestor = ein._requestor
	eout._responder = ein._responder
	eout._requestMessage = ein._requestMessage
}


// agrego un predicado por cada partición teórica posible
pred particionS0[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._state
}

pred particionS1[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Request
}

pred particionS2[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Respond
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

pred transicion_S2_a_IN_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


run transicion_S0_a_S0_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_S1_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_S2_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_IN_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message

run transicion_S1_a_S1_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_S0_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_S2_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_IN_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message

run transicion_S2_a_S2_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_S0_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_S1_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_IN_mediante_constructor for 2 EstadoConcreto, 4 Address, 4 Message

pred transicion_S0_a_S0_mediante_sendRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionSendRequest])
}

pred transicion_S0_a_S1_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}

pred transicion_S0_a_S2_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}

pred transicion_S0_a_IN_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}


pred transicion_S1_a_S1_mediante_sendRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionSendRequest])
}

pred transicion_S1_a_S0_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}

pred transicion_S1_a_S2_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}

pred transicion_S1_a_IN_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}


pred transicion_S2_a_S2_mediante_sendRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionSendRequest])
}

pred transicion_S2_a_S0_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}

pred transicion_S2_a_S1_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}

pred transicion_S2_a_IN_mediante_sendRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendRequest])
}


run transicion_S0_a_S0_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_S1_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_S2_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_IN_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message

run transicion_S1_a_S1_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_S0_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_S2_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_IN_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message

run transicion_S2_a_S2_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_S0_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_S1_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_IN_mediante_sendRequest for 2 EstadoConcreto, 4 Address, 4 Message

pred transicion_S0_a_S0_mediante_sendResponse{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionSendResponse])
}

pred transicion_S0_a_S1_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}

pred transicion_S0_a_S2_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}

pred transicion_S0_a_IN_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}


pred transicion_S1_a_S1_mediante_sendResponse{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionSendResponse])
}

pred transicion_S1_a_S0_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}

pred transicion_S1_a_S2_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}

pred transicion_S1_a_IN_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}


pred transicion_S2_a_S2_mediante_sendResponse{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionSendResponse])
}

pred transicion_S2_a_S0_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}

pred transicion_S2_a_S1_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}

pred transicion_S2_a_IN_mediante_sendResponse{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSendResponse])
}

run transicion_S0_a_S0_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_S1_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_S2_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S0_a_IN_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message

run transicion_S1_a_S1_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_S0_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_S2_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S1_a_IN_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message

run transicion_S2_a_S2_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_S0_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_S1_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
run transicion_S2_a_IN_mediante_sendResponse for 2 EstadoConcreto, 4 Address, 4 Message
