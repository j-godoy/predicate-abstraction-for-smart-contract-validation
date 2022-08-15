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

run transicion_S05_a_S08_mediante_met_bid for 2 EstadoConcreto

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


/*
pred invariante[e:EstadoConcreto] {
	//Una Address no puede tener balance negativo
	(no a:Address | a.balance < 0)
	
	(Address0x0 in e._pendingReturns.Int and e._pendingReturns[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.Int implies e._pendingReturns[a] >= 0)

	e._highestBid >= 0
	highestBidEslaApuestaMayor[e] or e._ended = True
	e._highestBidder in e._pendingReturns.Int

	e._auctionStart >= 0
	e._biddingTime >= 0
}

pred highestBidEslaApuestaMayor[e:EstadoConcreto] {
	(some a1:Address | a1 = e._highestBidder and a1 in e._pendingReturns.Int and
			(all a2:Address | a2 in e._pendingReturns.Int 
						implies e._pendingReturns[a1] >= e._pendingReturns[a2]
							and e._highestBid = e._pendingReturns[a1]
			)
	)
}
*/

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

/*pred highestBidEslaApuestaMayor[e:EstadoConcreto] {
	(e._highestBid = 0 and e._pendingReturns = Address0x0->0) or 
	(all a:Address | a in e._pendingReturns.Int
		implies e._pendingReturns[a] <= e._highestBid
	)
}*/

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
	eout._pendingReturns = ein._pendingReturns++ein._highestBidder->ein._pendingReturns[ein._highestBidder].add[ein._highestBid]
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
pred partitionS00[e: EstadoConcreto]{ // 
	//(invariante[e])
	(e._beneficiary = Address0x0)
}

pred partitionINV[e: EstadoConcreto]{
	not invariante[e]
}

pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e]
}

pred transicion_S00_a_S00_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S06_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S07_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_S08_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S00_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S00_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S00_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S06_a_INV_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S00_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S07_a_INV_mediante_met_constructor{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S00_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
}

pred transicion_S08_a_INV_mediante_met_constructor{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10, v11:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v11, v20, v21])
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
run transicion_S08_a_INV_mediante_met_constructor for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S06_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S07_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S08_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S06_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S07_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S08_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S06_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S07_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S08_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S06_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S07_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S08_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S00_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S06_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S07_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S08_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S00_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S06_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S07_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S08_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S00_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S01_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S02_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S03_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S04_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S05_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S06_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S07_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S08_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_INV_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S00_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S01_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S02_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S03_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S04_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S05_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S06_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S07_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S08_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_INV_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S00_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S01_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S02_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S03_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S04_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S05_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S06_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S07_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S08_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_INV_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
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
run transicion_S08_a_INV_mediante_met_bid for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
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
run transicion_S08_a_INV_mediante_met_withdraw for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S07_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S08_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_auctionEnd{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_INV_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S00_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_INV_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S00_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_INV_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
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
run transicion_S08_a_INV_mediante_met_auctionEnd for 2 EstadoConcreto
