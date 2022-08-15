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

run transicion_S01_a_S02_mediante_met_bid for 2 EstadoConcreto

// estados concretos
abstract sig EstadoConcreto {
	_auctionStart: Int,
	_biddingTime: Int,
	_beneficiary: Address,
	_highestBidder: Address,
	_highestBid: Int,
	_pendingReturns: Address -> lone Int,
	_ended: Bool,
	_now: Int //lo agrego para simular el paso del tiempo
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}

pred invarianteSinBeneficiary[e:EstadoConcreto] {
	//Una Address no puede tener balance negativo
	(no a:Address | a.balance < 0)
	
	(Address0x0 in e._pendingReturns.Int and e._pendingReturns[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.Int implies e._pendingReturns[a] >= 0)

	e._highestBid >= 0
//	highestBidEslaApuestaMayor[e] or #(e._pendingReturns.Int) = 1 //or e._ended = True

	e._auctionStart >= 0
	e._biddingTime >= 0

	e._highestBidder = Address0x0 implies #(e._pendingReturns.Int) = 1

	e._ended = True implies e._now > e._auctionStart.add[e._biddingTime]
}

pred invariante[e:EstadoConcreto] {
	invarianteSinBeneficiary[e]
	e._beneficiary = AddressBeneficiary
}

/*pred highestBidEslaApuestaMayor[e:EstadoConcreto] {
	(some a1:Address | a1 = e._highestBidder and a1 !in e._pendingReturns.Int and
			(all a2:Address | a2 in e._pendingReturns.Int implies
				e._highestBid >= e._pendingReturns[a2]
			)
	) or
	(some a1:Address | a1 = e._highestBidder and e._highestBid>0 and a1 in e._pendingReturns.Int and
		(all a2:Address | a2 in e._pendingReturns.Int implies
				e._pendingReturns[a1] >= e._pendingReturns[a2]
		)
	)
}*/

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int, biddingTime: Int ] {
	//Pre
	ein._beneficiary = Address0x0
	ein._highestBidder = Address0x0
	ein._highestBid = 0
	ein._pendingReturns = Address0x0 -> 0
	ein._ended = False

	//Post
	eout._auctionStart = 1
	eout._beneficiary = AddressBeneficiary
	eout._biddingTime = biddingTime

	//eout._auctionStart = ein._auctionStart
	//eout._biddingTime = ein._biddingTime
	//eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now.add[1]
}

pred pre_bid[ein:EstadoConcreto] {
	ein._now <= ein._auctionStart.add[ein._biddingTime]
	//(ein._beneficiary != Address0x0)
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_bid[ein]
	(ein._beneficiary != Address0x0)
	sender != Address0x0
	value > ein._highestBid

	//POST
	ein._highestBidder != Address0x0 =>
		(eout._pendingReturns = ein._pendingReturns++ein._highestBidder->ein._pendingReturns[ein._highestBidder].add[ein._highestBid])
	else
		(eout._pendingReturns = ein._pendingReturns)
	
	eout._highestBidder = sender
	eout._highestBid = value

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	//eout._highestBidder = ein._highestBidder
	//eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now.add[1]
}

pred pre_withdraw[ein: EstadoConcreto] {
	//highestBidEslaApuestaMayor[ein]
	some a:Address | a !=Address0x0 and a in ein._pendingReturns.Int
				and ein._pendingReturns[a] != 0
	//(ein._beneficiary != Address0x0)
}

pred met_withdrawA[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	ein._pendingReturns[sender] > 0
	(ein._beneficiary != Address0x0)
	sender != Address0x0
	sender in ein._pendingReturns.Int
	sender = AddressA

	//POST

	//(let pr = pendingReturns[sender] |
	eout._pendingReturns = ein._pendingReturns++sender -> 0

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now.add[1]
}


pred met_withdrawOther[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	ein._pendingReturns[sender] > 0
	(ein._beneficiary != Address0x0)
	sender != Address0x0
	sender in ein._pendingReturns.Int
	sender != AddressA

	//POST

	//(let pr = pendingReturns[sender] |
	eout._pendingReturns = ein._pendingReturns++sender -> 0

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now.add[1]
}

//pred auctionEndTime[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
//        ein = eout
//}

pred pre_auctionEnd[ein: EstadoConcreto] {
	(ein._now >= (ein._auctionStart.add[ein._biddingTime])) // auction did not yet end
	(ein._ended = False)
	(ein._beneficiary != Address0x0)
}

pred met_auctionEnd[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_auctionEnd[ein]
	sender != Address0x0

	//POST
	eout._ended = True
	//eout._beneficiary.balance = ein._beneficiary.balance.add[ein._highestBid]

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	//eout._ended = ein._ended
	eout._now = ein._now.add[1]
}


//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{ // 
	(invarianteSinBeneficiary[e])
	(e._beneficiary = Address0x0)
}

pred partitionINV[e: EstadoConcreto]{
	not invariante[e]
}


pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder = Address0x0)
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some a:Address | a in e._pendingReturns.Int and a = AddressA and e._highestBidder = a)
	e._highestBidder = AddressA
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some b:Address | b in e._pendingReturns.Int and b != AddressA and e._highestBidder = b)
	e._highestBidder != AddressA
}


pred partitionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder = Address0x0)
}

pred partitionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some a:Address | a in e._pendingReturns.Int and a = AddressA and e._highestBidder = a)
	e._highestBidder = AddressA
}

pred partitionS06[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some b:Address | b in e._pendingReturns.Int and b != AddressA and e._highestBidder = b)
	e._highestBidder != AddressA
}











pred transicion_S00_a_S00_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S06_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S00_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S00_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S00_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_constructor{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S00_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_constructor for 2 EstadoConcreto
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

run transicion_S00_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_bid for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_withdrawA{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_withdrawA{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_withdrawA{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_withdrawA{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_withdrawA{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_withdrawA{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_withdrawA{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_withdrawA{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_withdrawA{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_withdrawA{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_withdrawA{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_withdrawA{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_withdrawA{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_withdrawA{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_withdrawA{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_withdrawA{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_withdrawA{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_withdrawA{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_withdrawA{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_withdrawA{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_withdrawA{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_withdrawA{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_withdrawA{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_withdrawA{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_withdrawA{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_withdrawA{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_withdrawA{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_withdrawA{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_withdrawA{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_withdrawA{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_withdrawA{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_withdrawA{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_withdrawA{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_withdrawA{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_withdrawA{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_withdrawA{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_withdrawA{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_withdrawA{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_withdrawA{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_withdrawA{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_withdrawA{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_withdrawA{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_withdrawA{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_withdrawA{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_withdrawA{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_withdrawA{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_withdrawA{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_withdrawA{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_withdrawA{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawA [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_withdrawA for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_withdrawA for 2 EstadoConcreto
pred transicion_S00_a_S00_mediante_met_withdrawOther{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_withdrawOther{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_withdrawOther{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_withdrawOther{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_withdrawOther{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_withdrawOther{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S06_mediante_met_withdrawOther{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_withdrawOther{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_withdrawOther{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_withdrawOther{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_withdrawOther{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_withdrawOther{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_withdrawOther{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_withdrawOther{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_withdrawOther{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_withdrawOther{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_withdrawOther{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_withdrawOther{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_withdrawOther{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_withdrawOther{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_withdrawOther{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_withdrawOther{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_withdrawOther{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_withdrawOther{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_withdrawOther{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_withdrawOther{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_withdrawOther{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_withdrawOther{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_withdrawOther{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_withdrawOther{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_withdrawOther{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_withdrawOther{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_withdrawOther{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_withdrawOther{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_withdrawOther{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_withdrawOther{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_withdrawOther{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_withdrawOther{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_withdrawOther{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_withdrawOther{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_withdrawOther{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_withdrawOther{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S00_mediante_met_withdrawOther{
	(partitionS06[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_withdrawOther{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_withdrawOther{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_withdrawOther{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_withdrawOther{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_withdrawOther{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_withdrawOther{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdrawOther [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_withdrawOther for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_withdrawOther for 2 EstadoConcreto
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

run transicion_S00_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S00_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
