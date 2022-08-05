// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{transiciones: Accion -> set EstadoAbstracto}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}

//Acciones de los estados abstractos
abstract sig Accion{}
one sig AccionConstructor extends Accion {}
one sig AccionBeginReviewProcess extends Accion {}
one sig AccionRejectApplication extends Accion {}
one sig AccionUploadDocuments extends Accion {}
one sig AccionShareWithThirdParty extends Accion {}
one sig AccionAcceptSharingRequest extends Accion {}
one sig AccionRejectSharingRequest extends Accion {}
one sig AccionRequestLockerAccess extends Accion {}
one sig AccionReleaseLockerAccess extends Accion {}
one sig AccionRevokeAccessFromThirdParty extends Accion {}
one sig AccionTerminate extends Accion {}

// Describo cómo pasar de un estado a otro mediante cada acción
fact trans_accionConstructor{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionConstructor]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10,v11:Address,v20:Texto | constructor[e0,e1,v10,v11,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionBeginReviewProcess{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionBeginReviewProcess]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | beginReviewProcess[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionRejectApplication{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionRejectApplication]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Texto | rejectApplication[e0,e1,v10,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionUploadDocuments{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionUploadDocuments]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20,v21:Texto | uploadDocuments[e0,e1,v10,v20,v21]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionShareWithThirdParty{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionShareWithThirdParty]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10,v11:Address,v20,v21:Texto | shareWithThirdParty[e0,e1,v10,v11,v20,v21]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionAcceptSharingRequest{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionAcceptSharingRequest]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | acceptSharingRequest[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionRejectSharingRequest{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionRejectSharingRequest]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | rejectSharingRequest[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionRequestLockerAccess{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionRequestLockerAccess]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Texto | requestLockerAccess[e0,e1,v10,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionReleaseLockerAccess{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionReleaseLockerAccess]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | releaseLockerAccess[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionRevokeAccessFromThirdParty{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionRevokeAccessFromThirdParty]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | revokeAccessFromThirdParty[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionTerminate{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionTerminate]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | terminate[e0,e1,v10]
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
one sig TextoPending extends Texto{}
one sig TextoRejected extends Texto{}
one sig TextoApproved extends Texto{}
one sig TextoShared extends Texto{}
one sig TextoAvailable extends Texto{}
one sig TextoVacio extends Texto{}
one sig TextoOtro extends Texto{}

abstract sig EstadoContrato{}
one sig Requested extends EstadoContrato{}
one sig DocumentReview extends EstadoContrato{}
one sig AvailableToShare extends EstadoContrato{}
one sig SharingRequestPending extends EstadoContrato{}
one sig SharingWithThirdParty extends EstadoContrato{}
one sig Terminated extends EstadoContrato{}


abstract sig EstadoConcreto {
	_owner: lone Address,
	_bankAgent: lone Address,
	_lockerFriendlyName: lone Texto,
	_lockerIdentifier: lone Texto,
	_currentAuthorizedUser: lone Address,
	_expirationDate: lone Texto,
	_image: lone Texto,
	_thirdPartyRequestor: lone Address,
	_intendedPurpose: lone Texto,
	_lockerStatus: lone Texto,
	_rejectionReason: lone Texto,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


//fact {all x: Int | x > 0}

pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	(no disj a1,a2:Address | a1.name = a2.name)
}

pred constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, bankAgent: Address, lockerFriendlyName: Texto] {
	//Pre
	(no ein._owner and no ein._bankAgent and no ein._lockerFriendlyName
	and no ein._lockerIdentifier and no ein._currentAuthorizedUser and no ein._expirationDate
	and no ein._image and no ein._thirdPartyRequestor and no ein._intendedPurpose
	and no ein._lockerStatus and no ein._rejectionReason and no ein._state)
	//Post
	eout._owner = sender
	eout._lockerFriendlyName  = lockerFriendlyName
	eout._state = DocumentReview //////////////// should be StateType.Requested?
	eout._bankAgent = bankAgent

	//eout._owner = ein._owner
	//eout._bankAgent = ein._bankAgent
	//eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred beginReviewProcess[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._owner != sender
	//Post
	eout._owner = sender
	eout._bankAgent = sender
	eout._lockerStatus = TextoPending
	eout._state = DocumentReview

	//eout._owner = ein._owner
	//eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred rejectApplication[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, rejectionReason: Texto] {
	//Pre
	some ein._state
	ein._bankAgent = sender
	//Post
	eout._rejectionReason = rejectionReason
	eout._lockerStatus = TextoRejected
	eout._state = DocumentReview

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	//eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred uploadDocuments[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, lockerIdentifier: Texto, image: Texto] {
	//Pre
	some ein._state
	eout._bankAgent = sender
	//Post
	eout._lockerStatus = TextoApproved
	eout._image = image
	eout._lockerIdentifier = lockerIdentifier
	eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	//eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	//eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred shareWithThirdParty[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address,
				thirdPartyRequestor: Address, expirationDate: Texto, intendedPurpose: Texto] {
	//Pre
	some ein._state
	ein._owner = sender

	//Post
	eout._thirdPartyRequestor = thirdPartyRequestor
	eout._currentAuthorizedUser = thirdPartyRequestor
	eout._lockerStatus = TextoShared
	eout._intendedPurpose = intendedPurpose
	eout._expirationDate = expirationDate
	eout._state = SharingWithThirdParty

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	//eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	//eout._thirdPartyRequestor = ein._thirdPartyRequestor
	//eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred acceptSharingRequest[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state
	ein._owner = sender

	//Post
	eout._currentAuthorizedUser = ein._thirdPartyRequestor
	eout._state = SharingWithThirdParty

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred rejectSharingRequest[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state
	ein._owner = sender

	//Post
	ein._lockerStatus = TextoAvailable
	ein._currentAuthorizedUser = Address0
	eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred requestLockerAccess[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, intendedPurpose: Texto] {
	//Pre
	some ein._state
	ein._owner != sender
	//Post
        eout._thirdPartyRequestor = sender
        eout._intendedPurpose = intendedPurpose
        eout._state = SharingRequestPending

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	//eout._thirdPartyRequestor = ein._thirdPartyRequestor
	//eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred releaseLockerAccess[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._currentAuthorizedUser = sender
	//Post
	eout._lockerStatus = TextoAvailable
        eout._thirdPartyRequestor = Address0
        eout._currentAuthorizedUser = Address0
        eout._intendedPurpose = TextoVacio
        eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	//eout._thirdPartyRequestor = ein._thirdPartyRequestor
	//eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred revokeAccessFromThirdParty[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._owner = sender
	//Post
	eout._lockerStatus = TextoAvailable
	eout._currentAuthorizedUser = Address0
	eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred terminate[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._owner = sender
	//Post
	eout._currentAuthorizedUser = Address0
	eout._state = Terminated

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

// agrego un predicado por cada partición teórica posible
pred particionS00[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._state
}

pred particionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Requested
}

pred particionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = DocumentReview
}

pred particionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = AvailableToShare
}

pred particionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SharingRequestPending
}

pred particionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SharingWithThirdParty
}

pred particionS06[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Terminated
}

pred particionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}




// agregar un predicado para cada transición posible
/*
De S0 a SN con acción
*/
pred transicion_S00_a_S00_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S03_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S04_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S05_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S06_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S01_a_S01_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S03_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S04_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S05_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S06_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S02_a_S02_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S03_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S04_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S05_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S06_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S03_a_S03_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S03_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S03_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S03_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S03_a_S04_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S03_a_S05_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S03_a_S06_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S03_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S04_a_S04_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S04_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S04_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S04_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S04_a_S03_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S04_a_S05_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S04_a_S06_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S04_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S05_a_S05_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S05_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S05_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S05_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S05_a_S03_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S05_a_S04_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S05_a_S06_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S05_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S06_a_S06_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S06_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S06_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S06_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S06_a_S03_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S06_a_S04_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S06_a_S05_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S06_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


run transicion_S00_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_beginReviewProcess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S00_a_S01_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S00_a_S02_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S00_a_S03_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S00_a_S04_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S00_a_S05_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S00_a_S06_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S00_a_INV_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}


pred transicion_S01_a_S01_mediante_beginReviewProcess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S01_a_S00_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S01_a_S02_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S01_a_S03_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S01_a_S04_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S01_a_S05_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S01_a_S06_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S01_a_INV_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}


pred transicion_S02_a_S02_mediante_beginReviewProcess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S02_a_S00_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S02_a_S01_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S02_a_S03_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S02_a_S04_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S02_a_S05_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S02_a_S06_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S02_a_INV_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}


pred transicion_S03_a_S03_mediante_beginReviewProcess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S03_a_S00_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S03_a_S01_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S03_a_S02_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S03_a_S04_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S03_a_S05_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S03_a_S06_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S03_a_INV_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}


pred transicion_S04_a_S04_mediante_beginReviewProcess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S04_a_S00_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S04_a_S01_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S04_a_S02_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S04_a_S03_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S04_a_S05_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S04_a_S06_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S04_a_INV_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}


pred transicion_S05_a_S05_mediante_beginReviewProcess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S05_a_S00_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S05_a_S01_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S05_a_S02_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S05_a_S03_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S05_a_S04_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S05_a_S06_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S05_a_INV_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}


pred transicion_S06_a_S06_mediante_beginReviewProcess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S06_a_S00_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S06_a_S01_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S06_a_S02_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S06_a_S03_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S06_a_S04_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S06_a_S05_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}

pred transicion_S06_a_INV_mediante_beginReviewProcess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionBeginReviewProcess])
}


run transicion_S00_a_S00_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_beginReviewProcess for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_rejectApplication{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S00_a_S01_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S00_a_S02_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S00_a_S03_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S00_a_S04_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S00_a_S05_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S00_a_S06_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S00_a_INV_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}


pred transicion_S01_a_S01_mediante_rejectApplication{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S01_a_S00_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S01_a_S02_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S01_a_S03_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S01_a_S04_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S01_a_S05_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S01_a_S06_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S01_a_INV_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}


pred transicion_S02_a_S02_mediante_rejectApplication{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S02_a_S00_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S02_a_S01_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S02_a_S03_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S02_a_S04_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S02_a_S05_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S02_a_S06_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S02_a_INV_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}


pred transicion_S03_a_S03_mediante_rejectApplication{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S03_a_S00_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S03_a_S01_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S03_a_S02_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S03_a_S04_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S03_a_S05_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S03_a_S06_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S03_a_INV_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}


pred transicion_S04_a_S04_mediante_rejectApplication{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S04_a_S00_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S04_a_S01_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S04_a_S02_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S04_a_S03_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S04_a_S05_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S04_a_S06_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S04_a_INV_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}


pred transicion_S05_a_S05_mediante_rejectApplication{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S05_a_S00_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S05_a_S01_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S05_a_S02_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S05_a_S03_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S05_a_S04_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S05_a_S06_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S05_a_INV_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}


pred transicion_S06_a_S06_mediante_rejectApplication{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S06_a_S00_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S06_a_S01_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S06_a_S02_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S06_a_S03_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S06_a_S04_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S06_a_S05_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}

pred transicion_S06_a_INV_mediante_rejectApplication{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectApplication])
}


run transicion_S00_a_S00_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_rejectApplication for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_uploadDocuments{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S00_a_S01_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S00_a_S02_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S00_a_S03_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S00_a_S04_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S00_a_S05_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S00_a_S06_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S00_a_INV_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}


pred transicion_S01_a_S01_mediante_uploadDocuments{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S01_a_S00_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S01_a_S02_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S01_a_S03_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S01_a_S04_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S01_a_S05_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S01_a_S06_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S01_a_INV_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}


pred transicion_S02_a_S02_mediante_uploadDocuments{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S02_a_S00_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S02_a_S01_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S02_a_S03_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S02_a_S04_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S02_a_S05_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S02_a_S06_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S02_a_INV_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}


pred transicion_S03_a_S03_mediante_uploadDocuments{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S03_a_S00_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S03_a_S01_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S03_a_S02_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S03_a_S04_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S03_a_S05_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S03_a_S06_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S03_a_INV_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}


pred transicion_S04_a_S04_mediante_uploadDocuments{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S04_a_S00_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S04_a_S01_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S04_a_S02_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S04_a_S03_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S04_a_S05_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S04_a_S06_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S04_a_INV_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}


pred transicion_S05_a_S05_mediante_uploadDocuments{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S05_a_S00_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S05_a_S01_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S05_a_S02_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S05_a_S03_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S05_a_S04_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S05_a_S06_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S05_a_INV_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}


pred transicion_S06_a_S06_mediante_uploadDocuments{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S06_a_S00_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S06_a_S01_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S06_a_S02_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S06_a_S03_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S06_a_S04_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S06_a_S05_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}

pred transicion_S06_a_INV_mediante_uploadDocuments{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionUploadDocuments])
}


run transicion_S00_a_S00_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_uploadDocuments for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_shareWithThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S00_a_S01_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S00_a_S02_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S00_a_S03_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S00_a_S04_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S00_a_S05_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S00_a_S06_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S00_a_INV_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}


pred transicion_S01_a_S01_mediante_shareWithThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S01_a_S00_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S01_a_S02_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S01_a_S03_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S01_a_S04_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S01_a_S05_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S01_a_S06_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S01_a_INV_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}


pred transicion_S02_a_S02_mediante_shareWithThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S02_a_S00_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S02_a_S01_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S02_a_S03_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S02_a_S04_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S02_a_S05_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S02_a_S06_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S02_a_INV_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}


pred transicion_S03_a_S03_mediante_shareWithThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S03_a_S00_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S03_a_S01_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S03_a_S02_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S03_a_S04_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S03_a_S05_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S03_a_S06_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S03_a_INV_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}


pred transicion_S04_a_S04_mediante_shareWithThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S04_a_S00_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S04_a_S01_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S04_a_S02_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S04_a_S03_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S04_a_S05_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S04_a_S06_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S04_a_INV_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}


pred transicion_S05_a_S05_mediante_shareWithThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S05_a_S00_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S05_a_S01_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S05_a_S02_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S05_a_S03_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S05_a_S04_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S05_a_S06_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S05_a_INV_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}


pred transicion_S06_a_S06_mediante_shareWithThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S06_a_S00_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S06_a_S01_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S06_a_S02_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S06_a_S03_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S06_a_S04_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S06_a_S05_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}

pred transicion_S06_a_INV_mediante_shareWithThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionShareWithThirdParty])
}


run transicion_S00_a_S00_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_shareWithThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_acceptSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S00_a_S01_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S00_a_S02_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S00_a_S03_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S00_a_S04_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S00_a_S05_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S00_a_S06_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S00_a_INV_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}


pred transicion_S01_a_S01_mediante_acceptSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S01_a_S00_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S01_a_S02_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S01_a_S03_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S01_a_S04_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S01_a_S05_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S01_a_S06_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S01_a_INV_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}


pred transicion_S02_a_S02_mediante_acceptSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S02_a_S00_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S02_a_S01_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S02_a_S03_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S02_a_S04_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S02_a_S05_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S02_a_S06_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S02_a_INV_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}


pred transicion_S03_a_S03_mediante_acceptSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S03_a_S00_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S03_a_S01_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S03_a_S02_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S03_a_S04_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S03_a_S05_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S03_a_S06_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S03_a_INV_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}


pred transicion_S04_a_S04_mediante_acceptSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S04_a_S00_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S04_a_S01_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S04_a_S02_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S04_a_S03_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S04_a_S05_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S04_a_S06_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S04_a_INV_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}


pred transicion_S05_a_S05_mediante_acceptSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S05_a_S00_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S05_a_S01_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S05_a_S02_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S05_a_S03_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S05_a_S04_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S05_a_S06_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S05_a_INV_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}


pred transicion_S06_a_S06_mediante_acceptSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S06_a_S00_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S06_a_S01_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S06_a_S02_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S06_a_S03_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S06_a_S04_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S06_a_S05_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}

pred transicion_S06_a_INV_mediante_acceptSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionAcceptSharingRequest])
}


run transicion_S00_a_S00_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_acceptSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_rejectSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S00_a_S01_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S00_a_S02_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S00_a_S03_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S00_a_S04_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S00_a_S05_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S00_a_S06_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S00_a_INV_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}


pred transicion_S01_a_S01_mediante_rejectSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S01_a_S00_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S01_a_S02_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S01_a_S03_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S01_a_S04_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S01_a_S05_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S01_a_S06_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S01_a_INV_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}


pred transicion_S02_a_S02_mediante_rejectSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S02_a_S00_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S02_a_S01_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S02_a_S03_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S02_a_S04_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S02_a_S05_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S02_a_S06_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S02_a_INV_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}


pred transicion_S03_a_S03_mediante_rejectSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S03_a_S00_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S03_a_S01_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S03_a_S02_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S03_a_S04_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S03_a_S05_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S03_a_S06_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S03_a_INV_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}


pred transicion_S04_a_S04_mediante_rejectSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S04_a_S00_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S04_a_S01_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S04_a_S02_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S04_a_S03_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S04_a_S05_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S04_a_S06_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S04_a_INV_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}


pred transicion_S05_a_S05_mediante_rejectSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S05_a_S00_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S05_a_S01_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S05_a_S02_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S05_a_S03_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S05_a_S04_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S05_a_S06_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S05_a_INV_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}


pred transicion_S06_a_S06_mediante_rejectSharingRequest{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S06_a_S00_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S06_a_S01_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S06_a_S02_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S06_a_S03_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S06_a_S04_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S06_a_S05_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}

pred transicion_S06_a_INV_mediante_rejectSharingRequest{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRejectSharingRequest])
}


run transicion_S00_a_S00_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_rejectSharingRequest for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_requestLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S00_a_S01_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S00_a_S02_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S00_a_S03_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S00_a_S04_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S00_a_S05_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S00_a_S06_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S00_a_INV_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}


pred transicion_S01_a_S01_mediante_requestLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S01_a_S00_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S01_a_S02_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S01_a_S03_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S01_a_S04_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S01_a_S05_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S01_a_S06_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S01_a_INV_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}


pred transicion_S02_a_S02_mediante_requestLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S02_a_S00_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S02_a_S01_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S02_a_S03_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S02_a_S04_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S02_a_S05_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S02_a_S06_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S02_a_INV_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}


pred transicion_S03_a_S03_mediante_requestLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S03_a_S00_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S03_a_S01_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S03_a_S02_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S03_a_S04_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S03_a_S05_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S03_a_S06_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S03_a_INV_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}


pred transicion_S04_a_S04_mediante_requestLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S04_a_S00_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S04_a_S01_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S04_a_S02_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S04_a_S03_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S04_a_S05_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S04_a_S06_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S04_a_INV_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}


pred transicion_S05_a_S05_mediante_requestLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S05_a_S00_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S05_a_S01_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S05_a_S02_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S05_a_S03_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S05_a_S04_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S05_a_S06_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S05_a_INV_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}


pred transicion_S06_a_S06_mediante_requestLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S06_a_S00_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S06_a_S01_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S06_a_S02_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S06_a_S03_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S06_a_S04_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S06_a_S05_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}

pred transicion_S06_a_INV_mediante_requestLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRequestLockerAccess])
}


run transicion_S00_a_S00_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_requestLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_releaseLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S00_a_S01_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S00_a_S02_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S00_a_S03_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S00_a_S04_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S00_a_S05_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S00_a_S06_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S00_a_INV_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}


pred transicion_S01_a_S01_mediante_releaseLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S01_a_S00_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S01_a_S02_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S01_a_S03_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S01_a_S04_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S01_a_S05_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S01_a_S06_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S01_a_INV_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}


pred transicion_S02_a_S02_mediante_releaseLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S02_a_S00_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S02_a_S01_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S02_a_S03_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S02_a_S04_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S02_a_S05_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S02_a_S06_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S02_a_INV_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}


pred transicion_S03_a_S03_mediante_releaseLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S03_a_S00_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S03_a_S01_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S03_a_S02_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S03_a_S04_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S03_a_S05_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S03_a_S06_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S03_a_INV_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}


pred transicion_S04_a_S04_mediante_releaseLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S04_a_S00_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S04_a_S01_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S04_a_S02_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S04_a_S03_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S04_a_S05_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S04_a_S06_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S04_a_INV_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}


pred transicion_S05_a_S05_mediante_releaseLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S05_a_S00_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S05_a_S01_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S05_a_S02_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S05_a_S03_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S05_a_S04_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S05_a_S06_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S05_a_INV_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}


pred transicion_S06_a_S06_mediante_releaseLockerAccess{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S06_a_S00_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S06_a_S01_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S06_a_S02_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S06_a_S03_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S06_a_S04_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S06_a_S05_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}

pred transicion_S06_a_INV_mediante_releaseLockerAccess{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionReleaseLockerAccess])
}


run transicion_S00_a_S00_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_releaseLockerAccess for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_revokeAccessFromThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S00_a_S01_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S00_a_S02_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S00_a_S03_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S00_a_S04_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S00_a_S05_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S00_a_S06_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S00_a_INV_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}


pred transicion_S01_a_S01_mediante_revokeAccessFromThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S01_a_S00_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S01_a_S02_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S01_a_S03_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S01_a_S04_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S01_a_S05_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S01_a_S06_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S01_a_INV_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}


pred transicion_S02_a_S02_mediante_revokeAccessFromThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S02_a_S00_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S02_a_S01_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S02_a_S03_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S02_a_S04_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S02_a_S05_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S02_a_S06_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S02_a_INV_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}


pred transicion_S03_a_S03_mediante_revokeAccessFromThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S03_a_S00_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S03_a_S01_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S03_a_S02_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S03_a_S04_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S03_a_S05_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S03_a_S06_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S03_a_INV_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}


pred transicion_S04_a_S04_mediante_revokeAccessFromThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S04_a_S00_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S04_a_S01_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S04_a_S02_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S04_a_S03_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S04_a_S05_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S04_a_S06_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S04_a_INV_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}


pred transicion_S05_a_S05_mediante_revokeAccessFromThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S05_a_S00_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S05_a_S01_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S05_a_S02_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S05_a_S03_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S05_a_S04_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S05_a_S06_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S05_a_INV_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}


pred transicion_S06_a_S06_mediante_revokeAccessFromThirdParty{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S06_a_S00_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S06_a_S01_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S06_a_S02_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S06_a_S03_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S06_a_S04_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S06_a_S05_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}

pred transicion_S06_a_INV_mediante_revokeAccessFromThirdParty{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionRevokeAccessFromThirdParty])
}


run transicion_S00_a_S00_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_revokeAccessFromThirdParty for 2 EstadoConcreto, 5 Address, 7 Texto

pred transicion_S00_a_S00_mediante_terminate{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionTerminate])
}

pred transicion_S00_a_S01_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S00_a_S02_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S00_a_S03_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S00_a_S04_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S00_a_S05_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S00_a_S06_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S00_a_INV_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}


pred transicion_S01_a_S01_mediante_terminate{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionTerminate])
}

pred transicion_S01_a_S00_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S01_a_S02_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S01_a_S03_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S01_a_S04_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S01_a_S05_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S01_a_S06_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S01_a_INV_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}


pred transicion_S02_a_S02_mediante_terminate{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionTerminate])
}

pred transicion_S02_a_S00_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S02_a_S01_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S02_a_S03_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S02_a_S04_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S02_a_S05_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S02_a_S06_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S02_a_INV_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}


pred transicion_S03_a_S03_mediante_terminate{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS03[e]))
	(A0 in A0.transiciones[AccionTerminate])
}

pred transicion_S03_a_S00_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S03_a_S01_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S03_a_S02_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S03_a_S04_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S03_a_S05_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S03_a_S06_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S03_a_INV_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS03[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}


pred transicion_S04_a_S04_mediante_terminate{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS04[e]))
	(A0 in A0.transiciones[AccionTerminate])
}

pred transicion_S04_a_S00_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S04_a_S01_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S04_a_S02_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S04_a_S03_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S04_a_S05_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S04_a_S06_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S04_a_INV_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS04[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}


pred transicion_S05_a_S05_mediante_terminate{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS05[e]))
	(A0 in A0.transiciones[AccionTerminate])
}

pred transicion_S05_a_S00_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S05_a_S01_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S05_a_S02_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S05_a_S03_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S05_a_S04_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S05_a_S06_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS06[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S05_a_INV_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS05[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}


pred transicion_S06_a_S06_mediante_terminate{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS06[e]))
	(A0 in A0.transiciones[AccionTerminate])
}

pred transicion_S06_a_S00_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S06_a_S01_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S06_a_S02_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S06_a_S03_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS03[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S06_a_S04_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS04[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S06_a_S05_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS05[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}

pred transicion_S06_a_INV_mediante_terminate{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS06[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTerminate])
}


run transicion_S00_a_S00_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S01_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S02_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S03_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S04_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S05_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_S06_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S00_a_INV_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S01_a_S01_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S00_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S02_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S03_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S04_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S05_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_S06_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S01_a_INV_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S02_a_S02_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S00_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S01_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S03_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S04_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S05_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_S06_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S02_a_INV_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S03_a_S03_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S00_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S01_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S02_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S04_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S05_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_S06_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S03_a_INV_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S04_a_S04_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S00_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S01_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S02_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S03_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S05_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_S06_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S04_a_INV_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S05_a_S05_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S00_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S01_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S02_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S03_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S04_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_S06_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S05_a_INV_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto

run transicion_S06_a_S06_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S00_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S01_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S02_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S03_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S04_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_S05_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
run transicion_S06_a_INV_mediante_terminate for 2 EstadoConcreto, 5 Address, 7 Texto
