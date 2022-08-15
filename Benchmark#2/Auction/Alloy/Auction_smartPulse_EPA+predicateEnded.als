// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


// estados concretos
abstract sig Address{balance: Int}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}

//run transicion_S06_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}

abstract sig EstadoConcreto {
	_auctionStart: Int,
	_biddingTime: Int,
	_beneficiary: Address,
	_ended: Bool,
	_highestBidder: Address,
	_highestBid: Int,
	_pendingReturns: Address -> lone Int,
	_blockNumber: Int //lo agrego para simular el paso del tiempo
}


pred invariante[e:EstadoConcreto] {
	//Una Address no puede tener balance negativo
	(no a:Address | a.balance < 0)
	
	(Address0x0 in e._pendingReturns.Int and e._pendingReturns[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.Int implies e._pendingReturns[a] >= 0)

	e._highestBid >= 0
	not(e._highestBidder = Address0x0 and e._highestBid > 0)
	//highestBidEslaApuestaMayor[e]
	// or e._ended = True
	//e._highestBidder in e._pendingReturns.Int

	e._auctionStart >= 0
	e._biddingTime >= 0
}


pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
				beneficiary: Address, auctionStart: Int, biddingTime: Int] {
	//Pre
	ein._auctionStart = 0
	ein._biddingTime = 0
	ein._beneficiary = Address0x0
	ein._ended = False
	ein._highestBidder = Address0x0
	ein._highestBid = 0
	ein._pendingReturns = Address0x0 -> 0
	
	auctionStart >= 0
	biddingTime >= 0
	beneficiary != Address0x0
	

	//Post
	eout._auctionStart = auctionStart
	eout._biddingTime = biddingTime
	eout._beneficiary = beneficiary

	//eout._auctionStart = ein._auctionStart
	//eout._biddingTime = ein._biddingTime
	//eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber.add[1]
}

pred pre_bid[ein:EstadoConcreto] {
	//sender != Address0x0
	not(ein._auctionStart.add[ein._biddingTime] < ein._blockNumber or ein._ended = True)
	//not(value <= ein._highestBid)
	//highestBidEslaApuestaMayor[ein]
	(ein._beneficiary != Address0x0)
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_bid[ein]
	sender != Address0x0
	not(value <= ein._highestBid)

	//POST
	eout._pendingReturns = ein._pendingReturns++sender->ein._pendingReturns[sender].add[value]
	eout._highestBidder = sender
	eout._highestBid = value

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	//eout._highestBidder = ein._highestBidder
	//eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber.add[1]
}

pred pre_withdraw[ein: EstadoConcreto] {
	//sender != Address0x0
	//sender in ein._pendingReturns.Int
	//ein._pendingReturns[sender] != 0
	//highestBidEslaApuestaMayor[ein]
	some a:Address | a !=Address0x0 and a in ein._pendingReturns.Int
				and ein._pendingReturns[a] != 0
	(ein._beneficiary != Address0x0)
}

pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdraw[ein]
	sender != Address0x0
	sender in ein._pendingReturns.Int

	//POST

	//(let pr = pendingReturns[sender] |
	eout._pendingReturns = ein._pendingReturns++sender -> 0

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber.add[1]
}

pred pre_auctionEnd[ein: EstadoConcreto] {
	not (ein._blockNumber <= ein._auctionStart.add[ein._biddingTime]
		//or ein._ended = True) //FIX
	or ein._ended = False) //BUG
	(ein._beneficiary != Address0x0)
}

pred met_auctionEnd[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_auctionEnd[ein]
	sender != Address0x0

	//POST
	eout._ended = True
	eout._beneficiary = ein._beneficiary
	//eout._beneficiary.balance = ein._beneficiary.balance.add[ein._highestBid]

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	//eout._beneficiary = ein._beneficiary
	//eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber.add[1]
}


//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////
pred particionS00[e: EstadoConcreto]{ // 
	//(invariante[e])
	(e._beneficiary = Address0x0)
}

run particionS01

pred particionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = False)
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e]
}

pred particionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = False)
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e]
}

pred particionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = False)
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = False)
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS06[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = False)
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS07[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = False)
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e]
}

pred particionS08[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = False)
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e]
}


pred particionS09[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS10[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e]
}

pred particionS11[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e]
}

pred particionS12[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS13[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS14[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e]
}

pred particionS15[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e]
}

pred particionS16[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._beneficiary != Address0x0)
	(e._ended = True)
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e]
}

/*
pred particionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder = Address0x0)
}

pred particionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	(some a:Address | a in e._pendingReturns.Int and a = AddressA and e._highestBidder = a)
}

pred particionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	(some b:Address | b in e._pendingReturns.Int and b = AddressB and e._highestBidder = b)
}

pred particionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	(some c:Address | c in e._pendingReturns.Int and c != AddressA and c != AddressB
					and e._highestBidder = c)
}

pred particionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder = Address0x0)
}

pred particionS06[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	(some a:Address | a in e._pendingReturns.Int and a = AddressA and e._highestBidder = a)
}

pred particionS07[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	(some b:Address | b in e._pendingReturns.Int and b = AddressB and e._highestBidder = b)
}

pred particionS08[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	(some c:Address | c in e._pendingReturns.Int and c != AddressA and c != AddressB and e._highestBidder = c)
}
*/

pred particionINV[e: EstadoConcreto]{ // 
	(not invariante[e])
}

pred transicion_S00_a_S00_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S06_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S07_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S08_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S09_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S10_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S11_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S12_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S13_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S14_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S15_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S16_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S09_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S10_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S11_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S12_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S13_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S14_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S15_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S16_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_constructor{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S09_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S10_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S11_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S12_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S13_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S14_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S15_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S16_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_constructor{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S09_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S10_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S11_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S12_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S13_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S14_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S15_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S16_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_constructor{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S00_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S09_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S10_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S11_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S12_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S13_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S14_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S15_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S16_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_constructor{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S00_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S09_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S10_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S11_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S12_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S13_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S14_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S15_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S16_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_constructor{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S00_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S09_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S10_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S11_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S12_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S13_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S14_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S15_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S16_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_INV_mediante_met_constructor{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S00_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S09_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S10_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S11_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S12_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S13_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S14_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S15_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S16_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_INV_mediante_met_constructor{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S00_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S09_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S10_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S11_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S12_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S13_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S14_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S15_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S16_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_INV_mediante_met_constructor{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S00_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S01_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S02_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S03_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S04_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S05_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S06_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S07_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S08_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S09_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S10_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S11_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S12_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S13_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S14_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S15_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_S16_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S09_a_INV_mediante_met_constructor{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S00_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S01_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S02_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S03_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S04_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S05_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S06_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S07_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S08_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S09_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S10_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S11_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S12_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S13_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S14_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S15_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_S16_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S10_a_INV_mediante_met_constructor{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S00_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S01_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S02_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S03_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S04_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S05_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S06_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S07_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S08_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S09_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S10_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S11_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S12_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S13_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S14_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S15_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_S16_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S11_a_INV_mediante_met_constructor{
	(particionS11[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S00_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S01_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S02_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S03_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S04_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S05_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S06_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S07_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S08_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S09_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S10_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S11_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S12_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S13_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S14_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S15_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_S16_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S12_a_INV_mediante_met_constructor{
	(particionS12[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S00_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S01_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S02_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S03_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S04_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S05_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S06_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S07_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S08_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S09_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S10_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S11_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S12_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S13_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S14_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S15_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_S16_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S13_a_INV_mediante_met_constructor{
	(particionS13[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S00_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S01_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S02_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S03_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S04_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S05_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S06_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S07_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S08_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S09_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S10_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S11_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S12_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S13_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S14_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S15_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_S16_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S14_a_INV_mediante_met_constructor{
	(particionS14[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S00_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S01_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S02_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S03_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S04_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S05_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S06_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S07_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S08_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S09_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S10_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S11_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S12_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S13_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S14_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S15_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_S16_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S15_a_INV_mediante_met_constructor{
	(particionS15[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S00_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S01_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S02_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S03_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S04_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S05_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S06_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S07_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S08_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S09_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S10_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S11_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S12_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S13_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S14_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S15_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_S16_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S16_a_INV_mediante_met_constructor{
	(particionS16[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
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
run transicion_S00_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S01_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S02_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S03_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S04_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S05_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S06_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S07_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_constructor for 2 EstadoConcreto
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
run transicion_S08_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S09_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S10_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S11_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S12_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S13_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S14_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S15_a_INV_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_constructor for 2 EstadoConcreto
run transicion_S16_a_INV_mediante_met_constructor for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S06_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S07_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S08_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S09_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S10_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S11_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S12_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S13_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S14_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S15_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S16_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_bid{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S06_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S07_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S08_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S09_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S10_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S11_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S12_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S13_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S14_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S15_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S16_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_bid{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S06_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S07_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S08_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S09_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S10_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S11_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S12_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S13_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S14_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S15_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S16_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_bid{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S06_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S07_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S08_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S09_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S10_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S11_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S12_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S13_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S14_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S15_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S16_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_bid{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S00_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S06_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S07_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S08_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S09_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S10_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S11_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S12_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S13_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S14_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S15_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S16_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_bid{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S00_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S06_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S07_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S08_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S09_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S10_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S11_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S12_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S13_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S14_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S15_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S16_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_bid{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S00_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S01_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S02_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S03_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S04_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S05_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S06_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S07_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S08_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S09_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S10_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S11_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S12_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S13_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S14_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S15_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S16_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_INV_mediante_met_bid{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S00_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S01_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S02_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S03_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S04_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S05_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S06_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S07_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S08_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S09_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S10_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S11_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S12_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S13_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S14_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S15_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S16_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_INV_mediante_met_bid{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S00_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S01_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S02_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S03_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S04_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S05_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S06_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S07_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S08_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S09_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S10_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S11_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S12_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S13_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S14_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S15_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S16_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_INV_mediante_met_bid{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S00_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S01_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S02_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S03_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S04_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S05_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S06_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S07_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S08_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S09_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S10_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S11_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S12_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S13_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S14_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S15_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S16_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_INV_mediante_met_bid{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S00_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S01_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S02_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S03_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S04_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S05_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S06_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S07_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S08_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S09_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S10_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S11_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S12_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S13_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S14_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S15_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S16_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_INV_mediante_met_bid{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S00_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S01_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S02_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S03_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S04_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S05_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S06_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S07_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S08_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S09_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S10_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S11_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S12_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S13_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S14_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S15_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S16_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_INV_mediante_met_bid{
	(particionS11[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S00_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S01_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S02_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S03_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S04_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S05_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S06_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S07_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S08_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S09_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S10_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S11_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S12_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S13_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S14_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S15_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S16_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_INV_mediante_met_bid{
	(particionS12[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S00_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S01_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S02_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S03_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S04_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S05_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S06_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S07_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S08_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S09_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S10_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S11_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S12_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S13_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S14_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S15_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S16_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_INV_mediante_met_bid{
	(particionS13[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S00_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S01_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S02_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S03_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S04_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S05_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S06_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S07_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S08_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S09_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S10_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S11_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S12_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S13_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S14_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S15_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S16_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_INV_mediante_met_bid{
	(particionS14[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S00_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S01_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S02_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S03_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S04_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S05_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S06_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S07_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S08_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S09_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S10_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S11_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S12_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S13_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S14_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S15_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S16_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_INV_mediante_met_bid{
	(particionS15[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S00_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S01_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S02_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S03_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S04_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S05_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S06_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S07_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S08_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S09_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S10_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S11_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S12_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S13_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S14_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S15_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S16_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_INV_mediante_met_bid{
	(particionS16[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_INV_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_INV_mediante_met_bid for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S11_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S12_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S13_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S14_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S15_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S16_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_withdraw{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S11_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S12_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S13_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S14_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S15_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S16_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_withdraw{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S11_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S12_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S13_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S14_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S15_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S16_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_withdraw{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S11_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S12_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S13_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S14_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S15_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S16_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_withdraw{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S11_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S12_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S13_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S14_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S15_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S16_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_withdraw{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S11_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S12_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S13_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S14_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S15_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S16_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_withdraw{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S11_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S12_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S13_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S14_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S15_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S16_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_withdraw{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S11_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S12_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S13_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S14_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S15_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S16_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_withdraw{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S11_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S12_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S13_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S14_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S15_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S16_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_withdraw{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S11_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S12_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S13_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S14_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S15_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S16_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_withdraw{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S11_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S12_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S13_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S14_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S15_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S16_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_withdraw{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S00_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S01_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S02_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S03_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S04_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S05_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S06_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S07_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S08_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S09_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S10_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S11_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S12_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S13_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S14_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S15_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S16_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_INV_mediante_met_withdraw{
	(particionS11[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S00_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S01_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S02_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S03_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S04_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S05_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S06_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S07_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S08_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S09_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S10_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S11_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S12_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S13_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S14_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S15_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S16_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_INV_mediante_met_withdraw{
	(particionS12[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S00_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S01_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S02_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S03_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S04_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S05_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S06_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S07_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S08_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S09_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S10_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S11_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S12_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S13_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S14_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S15_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S16_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_INV_mediante_met_withdraw{
	(particionS13[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S00_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S01_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S02_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S03_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S04_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S05_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S06_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S07_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S08_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S09_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S10_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S11_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S12_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S13_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S14_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S15_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S16_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_INV_mediante_met_withdraw{
	(particionS14[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S00_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S01_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S02_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S03_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S04_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S05_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S06_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S07_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S08_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S09_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S10_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S11_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S12_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S13_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S14_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S15_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S16_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_INV_mediante_met_withdraw{
	(particionS15[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S00_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S01_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S02_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S03_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S04_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S05_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S06_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S07_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S08_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S09_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S10_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S11_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S12_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S13_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S14_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S15_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S16_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_INV_mediante_met_withdraw{
	(particionS16[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_INV_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S00_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_INV_mediante_met_withdraw for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S09_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S10_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S11_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S12_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S13_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S14_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S15_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S16_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_auctionEnd{
	(particionS00[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S11_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S12_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S13_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S14_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S15_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S16_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_auctionEnd{
	(particionS01[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S11_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S12_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S13_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S14_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S15_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S16_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_auctionEnd{
	(particionS02[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S11_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S12_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S13_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S14_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S15_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S16_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_auctionEnd{
	(particionS03[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S11_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S12_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S13_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S14_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S15_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S16_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_auctionEnd{
	(particionS04[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S11_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S12_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S13_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S14_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S15_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S16_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_auctionEnd{
	(particionS05[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S11_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S12_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S13_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S14_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S15_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S16_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_auctionEnd{
	(particionS06[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S11_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S12_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S13_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S14_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S15_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S16_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_auctionEnd{
	(particionS07[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S11_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S12_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S13_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S14_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S15_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S16_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_auctionEnd{
	(particionS08[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S00_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S11_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S12_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S13_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S14_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S15_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S16_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_INV_mediante_met_auctionEnd{
	(particionS09[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S00_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S11_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S12_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S13_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S14_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S15_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S16_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_INV_mediante_met_auctionEnd{
	(particionS10[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S00_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S01_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S02_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S03_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S04_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S05_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S06_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S07_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S08_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S09_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S10_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S11_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S12_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S13_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S14_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S15_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S16_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_INV_mediante_met_auctionEnd{
	(particionS11[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S00_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S01_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S02_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S03_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S04_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S05_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S06_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S07_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S08_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S09_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S10_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S11_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S12_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S13_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S14_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S15_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S16_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_INV_mediante_met_auctionEnd{
	(particionS12[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S00_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S01_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S02_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S03_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S04_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S05_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S06_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S07_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S08_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S09_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S10_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S11_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S12_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S13_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S14_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S15_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S16_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_INV_mediante_met_auctionEnd{
	(particionS13[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S00_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S01_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S02_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S03_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S04_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S05_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S06_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S07_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S08_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S09_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S10_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S11_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S12_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S13_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S14_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S15_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S16_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_INV_mediante_met_auctionEnd{
	(particionS14[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S00_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S01_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S02_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S03_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S04_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S05_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S06_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S07_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S08_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S09_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S10_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S11_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S12_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S13_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S14_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S15_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S16_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_INV_mediante_met_auctionEnd{
	(particionS15[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S00_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS00[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S01_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS01[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S02_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS02[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S03_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS03[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S04_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS04[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S05_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS05[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S06_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS06[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S07_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS07[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S08_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS08[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S09_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS09[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S10_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS10[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S11_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS11[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S12_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS12[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S13_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS13[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S14_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS14[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S15_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS15[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S16_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionS16[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_INV_mediante_met_auctionEnd{
	(particionS16[EstadoConcretoInicial])
	(particionINV[EstadoConcretoFinal])
	(some v10:Address | met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
