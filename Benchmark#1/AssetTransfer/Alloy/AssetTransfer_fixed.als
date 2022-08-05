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

abstract sig Texto{}
one sig TextoA extends Texto{}
one sig TextoB extends Texto{}
one sig TextoC extends Texto{}
one sig TextoD extends Texto{}

abstract sig EstadoContrato{}
one sig Active extends EstadoContrato{}
one sig OfferPlaced extends EstadoContrato{}
one sig PendingInspection extends EstadoContrato{}
one sig Inspected extends EstadoContrato{}
one sig Appraised extends EstadoContrato{}
one sig NotionalAcceptance extends EstadoContrato{}
one sig BuyerAccepted extends EstadoContrato{}
one sig SellerAccepted extends EstadoContrato{}
one sig Accepted extends EstadoContrato{}
one sig Terminated extends EstadoContrato{}


abstract sig EstadoConcreto {
	_instanceOwner: lone Address,
	_description: lone Texto,
	_askingPrice: lone Int,
	_instanceBuyer: lone Address,
	_offerPrice: lone Int,
	_instanceInspector: lone Address,
	_instanceAppraiser: lone Address,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


//fact {all x: Int | x > 0}

pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	(no disj a1,a2:Address | a1.name = a2.name)
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, description: Texto, price: Int] {
	//Pre
	no ein._state and no ein._instanceOwner and no  ein._description and no ein._askingPrice
	no ein._instanceBuyer and no ein._offerPrice and no ein._instanceInspector and no ein._instanceAppraiser
	//Post
	eout._instanceOwner = sender
	eout._askingPrice = price
	eout._description = description
	eout._state = Active

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
}

pred met_terminate[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._instanceOwner = sender
	ein._state != Terminated and ein._state != Accepted and ein._state != SellerAccepted// agrego FIX
	//Post
        eout._state = Terminated

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
}

pred met_modify[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, description: Texto, price: Int] {
	//Pre
	some ein._state
	ein._instanceOwner = sender
        ein._state =Active
	//Post
        eout._description = description
        eout._askingPrice = price

	eout._instanceOwner = ein._instanceOwner
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._state = ein._state
}

pred met_makeOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, inspector: Address,
		appraiser: Address, offerPrice: Int] {
	//Pre
	some ein._state
	ein._instanceOwner != sender
	ein._state =Active
	inspector != Address0 and appraiser != Address0 and offerPrice != 0
	//Post
	eout._instanceBuyer = sender
	eout._instanceInspector = inspector
	eout._instanceAppraiser = appraiser
	eout._offerPrice = offerPrice
	eout._state = OfferPlaced
	
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
}

pred met_acceptOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state
	ein._instanceOwner = sender
	ein._state = OfferPlaced
	//Post
	eout._state = PendingInspection
	eout._instanceBuyer = ein._instanceBuyer
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._offerPrice = ein._offerPrice
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
}

pred met_reject[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state
	(ein._state = OfferPlaced or ein._state = PendingInspection or ein._state = Inspected 
	   or ein._state = Appraised or ein._state = NotionalAcceptance or ein._state = BuyerAccepted)
	ein._instanceOwner = sender

	//Post
	eout._instanceBuyer = Address0
	eout._state = Active

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
}

pred met_accept[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state
	(ein._instanceOwner = sender or ein._instanceBuyer = sender)
	(sender != ein._instanceOwner or ein._state = NotionalAcceptance or ein._state = BuyerAccepted)
	(sender != ein._instanceBuyer or ein._state = NotionalAcceptance or ein._state = SellerAccepted)

	//Post
        (sender = ein._instanceBuyer) =>
		(
	         	(ein._state = NotionalAcceptance) => (eout._state = BuyerAccepted)
			else (
					(ein._state = SellerAccepted) => (eout._state = Accepted)
					else (eout._state = ein._state)
				)
		)
	else
		(
	         	(ein._state = NotionalAcceptance) => (eout._state = SellerAccepted)
			else (
					(ein._state = BuyerAccepted) => (eout._state = Accepted)
					else (eout._state = ein._state)
				)
		)

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
    }

pred met_modifyOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, offerPrice: Int] {
	//Pre
	some ein._state
	ein._state = OfferPlaced
	(ein._instanceBuyer = sender or offerPrice != 0)
	//Post
        eout._offerPrice = offerPrice

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceBuyer = ein._instanceBuyer
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._state = ein._state
}

pred met_rescindOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	(ein._state = OfferPlaced or ein._state = PendingInspection or ein._state = Inspected
		or ein._state = Appraised or ein._state = NotionalAcceptance or ein._state = SellerAccepted)
	ein._instanceBuyer = sender
	//Post
	eout._instanceBuyer = Address0
        eout._offerPrice = 0
        eout._state = Active

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
}

pred met_markAppraised[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._instanceAppraiser = sender
	ein._state = PendingInspection or ein._state = Inspected
	//Post
	(ein._state = PendingInspection) => (eout._state = Appraised)
	else
		(ein._state = Inspected) => (eout._state =  NotionalAcceptance)
		else (eout._state = ein._state)

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
}

pred met_markInspected[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	ein._instanceInspector = sender
	ein._state = PendingInspection or ein._state = Appraised
	//Post
	(ein._state = PendingInspection) => (eout._state = Inspected)
	else 
		(ein._state = Appraised) => (eout._state =  NotionalAcceptance)
		else (eout._state = ein._state)

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
}

// agrego un predicado por cada partición teórica posible
pred particionS00[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._state
}

pred particionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Active
}

pred particionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = OfferPlaced
}

pred particionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = PendingInspection
}

pred particionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Inspected
}

pred particionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Appraised
}

pred particionS06[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = NotionalAcceptance
}

pred particionS07[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SellerAccepted
}

pred particionS08[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = BuyerAccepted
}

pred particionS09[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Accepted
}

pred particionS10[e: EstadoConcreto]{ // 
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
pred transicion_S00_a_S00_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S06_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S07_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S08_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S09_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S10_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S03_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S04_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S05_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S06_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S07_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S08_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S09_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S10_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_INV_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S03_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S04_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S05_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S06_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S07_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S08_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S09_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S10_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_INV_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S00_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S01_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S02_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S03_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S04_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S05_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S06_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S07_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S08_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S09_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S10_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_INV_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S00_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S01_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S02_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S03_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S04_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S05_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S06_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S07_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S08_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S09_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S10_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_INV_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S00_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S01_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S02_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S03_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S04_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S05_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S06_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S07_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S08_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S09_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S10_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_INV_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S00_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S01_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S02_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S03_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S04_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S05_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S06_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S07_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S08_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S09_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S10_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_INV_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S00_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S01_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S02_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S03_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S04_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S05_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S06_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S07_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S08_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S09_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S10_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_INV_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S00_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S01_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S02_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S03_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S04_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S05_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S06_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S07_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S08_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S09_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S10_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_INV_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S00_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S01_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S02_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S03_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S04_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S05_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S06_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S07_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S08_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S09_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S10_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_INV_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S00_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S01_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S02_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S03_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S04_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S05_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S06_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S07_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S08_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S09_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S10_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_INV_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

run transicion_S00_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_constructor for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_constructor for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_terminate{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_terminate{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_terminate{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_terminate{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_terminate{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_terminate{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_terminate{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_terminate{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_terminate{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_terminate{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_terminate{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_terminate [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_terminate for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_terminate for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S01_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S02_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S03_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S04_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S05_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S06_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S07_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S08_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S09_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_S10_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S00_a_INV_mediante_met_modify{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S00_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S01_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S02_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S03_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S04_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S05_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S06_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S07_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S08_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S09_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_S10_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S01_a_INV_mediante_met_modify{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S00_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S01_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S02_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S03_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S04_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S05_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S06_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S07_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S08_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S09_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_S10_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S02_a_INV_mediante_met_modify{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S00_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S01_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S02_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S03_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S04_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S05_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S06_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S07_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S08_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S09_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_S10_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S03_a_INV_mediante_met_modify{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S00_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S01_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S02_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S03_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S04_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S05_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S06_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S07_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S08_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S09_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_S10_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S04_a_INV_mediante_met_modify{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S00_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S01_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S02_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S03_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S04_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S05_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S06_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S07_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S08_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S09_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_S10_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S05_a_INV_mediante_met_modify{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S00_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S01_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S02_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S03_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S04_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S05_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S06_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S07_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S08_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S09_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_S10_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S06_a_INV_mediante_met_modify{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S00_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S01_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S02_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S03_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S04_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S05_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S06_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S07_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S08_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S09_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_S10_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S07_a_INV_mediante_met_modify{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S00_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S01_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S02_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S03_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S04_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S05_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S06_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S07_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S08_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S09_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_S10_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S08_a_INV_mediante_met_modify{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S00_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S01_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S02_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S03_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S04_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S05_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S06_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S07_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S08_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S09_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_S10_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S09_a_INV_mediante_met_modify{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S00_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S01_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S02_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S03_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S04_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S05_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S06_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S07_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S08_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S09_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_S10_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

pred transicion_S10_a_INV_mediante_met_modify{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Texto, v30:Int | met_modify [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v30])
}

run transicion_S00_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_modify for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_modify for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S01_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S02_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S03_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S04_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S05_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S06_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S07_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S08_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S09_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_S10_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S00_a_INV_mediante_met_makeOffer{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S00_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S01_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S02_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S03_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S04_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S05_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S06_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S07_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S08_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S09_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_S10_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S01_a_INV_mediante_met_makeOffer{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S00_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S01_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S02_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S03_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S04_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S05_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S06_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S07_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S08_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S09_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_S10_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S02_a_INV_mediante_met_makeOffer{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S00_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S01_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S02_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S03_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S04_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S05_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S06_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S07_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S08_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S09_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_S10_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S03_a_INV_mediante_met_makeOffer{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S00_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S01_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S02_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S03_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S04_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S05_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S06_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S07_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S08_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S09_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_S10_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S04_a_INV_mediante_met_makeOffer{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S00_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S01_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S02_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S03_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S04_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S05_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S06_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S07_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S08_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S09_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_S10_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S05_a_INV_mediante_met_makeOffer{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S00_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S01_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S02_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S03_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S04_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S05_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S06_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S07_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S08_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S09_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_S10_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S06_a_INV_mediante_met_makeOffer{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S00_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S01_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S02_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S03_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S04_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S05_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S06_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S07_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S08_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S09_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_S10_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S07_a_INV_mediante_met_makeOffer{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S00_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S01_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S02_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S03_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S04_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S05_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S06_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S07_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S08_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S09_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_S10_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S08_a_INV_mediante_met_makeOffer{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S00_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S01_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S02_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S03_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S04_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S05_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S06_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S07_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S08_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S09_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_S10_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S09_a_INV_mediante_met_makeOffer{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S00_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S01_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S02_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S03_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S04_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S05_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S06_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S07_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S08_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S09_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_S10_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

pred transicion_S10_a_INV_mediante_met_makeOffer{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11, v12:Address, v20:Int | met_makeOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v12, v20])
}

run transicion_S00_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_makeOffer for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_acceptOffer{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_acceptOffer{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_acceptOffer{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_acceptOffer{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_acceptOffer{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_acceptOffer{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_acceptOffer{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_acceptOffer{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_acceptOffer{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_acceptOffer{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_acceptOffer{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_acceptOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_acceptOffer for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_reject{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_reject{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_reject{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_reject{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_reject{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_reject{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_reject{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_reject{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_reject{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_reject{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_reject{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_reject [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_reject for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_reject for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_accept{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_accept{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_accept{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_accept{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_accept{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_accept{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_accept{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_accept{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_accept{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_accept{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_accept{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_accept [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_accept for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_accept for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S06_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S07_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S08_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S09_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S10_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_modifyOffer{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S06_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S07_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S08_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S09_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S10_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_modifyOffer{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S06_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S07_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S08_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S09_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S10_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_modifyOffer{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S06_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S07_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S08_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S09_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S10_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_modifyOffer{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S00_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S06_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S07_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S08_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S09_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S10_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_modifyOffer{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S00_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S06_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S07_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S08_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S09_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S10_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_modifyOffer{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S00_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S01_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S02_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S03_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S04_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S05_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S06_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S07_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S08_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S09_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S10_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_INV_mediante_met_modifyOffer{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S00_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S01_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S02_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S03_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S04_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S05_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S06_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S07_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S08_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S09_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S10_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_INV_mediante_met_modifyOffer{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S00_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S01_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S02_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S03_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S04_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S05_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S06_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S07_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S08_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S09_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S10_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_INV_mediante_met_modifyOffer{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S00_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S01_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S02_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S03_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S04_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S05_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S06_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S07_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S08_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S09_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S10_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_INV_mediante_met_modifyOffer{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S00_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S01_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S02_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S03_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S04_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S05_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S06_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S07_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S08_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S09_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S10_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_INV_mediante_met_modifyOffer{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_modifyOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_modifyOffer for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_rescindOffer{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_rescindOffer{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_rescindOffer{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_rescindOffer{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_rescindOffer{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_rescindOffer{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_rescindOffer{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_rescindOffer{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_rescindOffer{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_rescindOffer{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_rescindOffer{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_rescindOffer [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_rescindOffer for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_markAppraised{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_markAppraised{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_markAppraised{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_markAppraised{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_markAppraised{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_markAppraised{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_markAppraised{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_markAppraised{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_markAppraised{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_markAppraised{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_markAppraised{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markAppraised [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_markAppraised for 2 EstadoConcreto, 5 Address
pred transicion_S00_a_S00_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_markInspected{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_markInspected{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_markInspected{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_markInspected{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_markInspected{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_markInspected{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_markInspected{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_markInspected{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_markInspected{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_markInspected{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_markInspected{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_markInspected [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S03_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S04_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S05_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S06_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S07_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S08_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S09_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S00_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S01_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S02_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S03_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S04_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S05_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S06_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S07_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S08_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S09_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_S10_mediante_met_markInspected for 2 EstadoConcreto, 5 Address
run transicion_S10_a_INV_mediante_met_markInspected for 2 EstadoConcreto, 5 Address