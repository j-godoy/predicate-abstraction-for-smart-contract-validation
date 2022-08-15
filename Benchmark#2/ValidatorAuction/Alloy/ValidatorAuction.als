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
one sig AddressC extends Address{}


abstract sig AuctionState {}
one sig Deployed extends AuctionState{}
one sig Started extends AuctionState{}
one sig DepositPending extends AuctionState{} /* all slots sold, someone needs to call depositBids */
one sig Ended extends AuctionState{}
one sig Failed extends AuctionState{}

sig DepositLocker{}

// estados concretos
abstract sig EstadoConcreto {
	//Ownable
	_owner: Address,
	//DepositLocker
	_initialized: DepositLocker ->Bool,
	_deposited: DepositLocker->Bool,
	_slasher: DepositLocker->Address,
	_depositorsProxy: DepositLocker->Address,
	_releaseTimestamp: DepositLocker->Int,
	_canWithdraw: DepositLocker->(Address -> Bool),
	_numberOfDepositors: DepositLocker->Int,
	_valuePerDepositor: DepositLocker->Int,
	//ValidatorAuction
	_auctionDurationInDays: Int,
	_startPrice: Int,
	_minimalNumberOfParticipants: Int,
	_maximalNumberOfParticipants: Int,
	_auctionState: lone AuctionState,
    	_depositLocker: DepositLocker,
    	_whitelist: Address->Bool,
	_bids: Address -> Int,
    	_bidders: seq Address,
	_startTime: Int,
	_closeTime: Int,
	_lowestSlotPrice: Int,
	_now: Int //lo agrego para simular el paso del tiempo
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


pred invariante [e:EstadoConcreto] {
	
}


pred onlyOwner[e: EstadoConcreto, sender: Address] {
	sender = e._owner
}

pred isInitialised[e: EstadoConcreto] {
	e._initialized[e._depositLocker] = True
}

pred isDeposited[e: EstadoConcreto] {
	e._deposited[e._depositLocker] = True
}

pred isNotDeposited[e: EstadoConcreto] {
	e._deposited[e._depositLocker] = False
}

pred onlyDepositorsProxy[e: EstadoConcreto, sender: Address] {
	sender = e._depositorsProxy[e._depositLocker]
}

pred init[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, slasher: Address,
			depositorsProxy: Address, releaseTimestamp: Int] {
	//PRE
	onlyOwner[ein, sender]
	not isInitialised[ein]
	releaseTimestamp > ein._now

	//POST
        eout._releaseTimestamp[ein._depositLocker] = releaseTimestamp
        eout._slasher[ein._depositLocker] = slasher
        eout._depositorsProxy[ein._depositLocker] = depositorsProxy
        eout._initialized[ein._depositLocker] = True
        eout._owner = Address0x0

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	//eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	//eout._slasher = ein._slasher
	//eout._depositorsProxy = ein._depositorsProxy
	//eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now.add[1]
}

pred registerDepositor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, depositor: Address] {
	//PRE
	isInitialised[ein]
	isNotDeposited[ein]
	onlyDepositorsProxy[ein, sender]
	ein._canWithdraw[ein._depositLocker][depositor] = False

	//POST
	eout._canWithdraw[ein._depositLocker] = ein._canWithdraw[ein._depositLocker]++depositor->True
	eout._numberOfDepositors[ein._depositLocker] = ein._numberOfDepositors[ein._depositLocker].add[1]

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	//eout._canWithdraw = ein._canWithdraw
	//eout._numberOfDepositors = ein._numberOfDepositors
	//eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now.add[1]
}

pred deposit[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int, valuePerDepositor: Int] {
	//PRE
	isInitialised[ein]
	isNotDeposited[ein]
	onlyDepositorsProxy[ein, sender]
	ein._numberOfDepositors[ein._depositLocker] > 0
	valuePerDepositor > 0
	let depositAmount = ein._numberOfDepositors[ein._depositLocker].mul[valuePerDepositor] |
				valuePerDepositor = depositAmount.div[ein._numberOfDepositors[ein._depositLocker]]
		and value = depositAmount

	//POST
	eout._valuePerDepositor[ein._depositLocker] = valuePerDepositor
	eout._deposited[ein._depositLocker] = True

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	//eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	//eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now.add[1]
}

pred withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	isInitialised[ein]
	isDeposited[ein]
	ein._now >= ein._releaseTimestamp[ein._depositLocker]
	ein._canWithdraw[ein._depositLocker][sender] = True

	//POST
	eout._canWithdraw[ein._depositLocker] = ein._canWithdraw[ein._depositLocker]++sender->False
        //msg.sender.transfer(valuePerDepositor);

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	//eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now.add[1]
}

pred slash[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, depositorToBeSlashed: Address] {
	//PRE
	isInitialised[ein]
	isDeposited[ein]
	sender = ein._slasher[ein._depositLocker]
	ein._canWithdraw[ein._depositLocker][depositorToBeSlashed] = True

	//POST
	eout._canWithdraw[ein._depositLocker] = ein._canWithdraw[ein._depositLocker]++depositorToBeSlashed->False
        //address(0).transfer(valuePerDepositor);

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	//eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now.add[1]
}

/////////////////////////////////
/////ValidatorAuction
////////////////////////////////
pred stateIs[e: EstadoConcreto, state: AuctionState] {
	e._auctionState = state
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, startPriceInWei: Int,
        auctionDurationInDays: Int, minimalNumberOfParticipants: Int, maximalNumberOfParticipants: Int,
        depositLocker: DepositLocker] {
	//PRE
	no ein._auctionState
	auctionDurationInDays > 0
	//auctionDurationInDays < 100.mul[365] //En alloy no tiene sentido
	minimalNumberOfParticipants > 0
	maximalNumberOfParticipants > 0
	minimalNumberOfParticipants <= maximalNumberOfParticipants
	//startPriceInWei < 10.mul[30] //En alloy no tiene sentido

	//POST
	eout._startPrice = startPriceInWei
	eout._auctionDurationInDays = auctionDurationInDays
	eout._maximalNumberOfParticipants = maximalNumberOfParticipants
	eout._minimalNumberOfParticipants = minimalNumberOfParticipants
	eout._depositLocker = depositLocker
	eout._auctionState = Deployed

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	//eout._auctionDurationInDays = ein._auctionDurationInDays
	//eout._startPrice = ein._startPrice
	//eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	//eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
    	//eout._depositLocker = ein._depositLocker
    	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
    	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now.add[1] //lo agrego para simular el paso del tiempo
}

/*pred currentPrice[ein: EstadoConcreto, price: Int] {
	stateIs[ein, Started]
	ein._now >= ein._startTime
        
	let secondsSinceStart = ein._now.sub[ein._startTime] |
	priceAtElapsedTime[ein, secondsSinceStart, price]
}

pred priceAtElapsedTime[ein: EstadoConcreto, secondsSinceStart: Int, price: Int] {
        // To prevent overflows
	secondsSinceStart < 100.mul[365]
	let msSinceStart = 1000.mul[secondsSinceStart] | 
	     let relativeAuctionTime = msSinceStart.div[ein._auctionDurationInDays] |
        		let decayDivisor = 2 | //746571428571 | 
		     let decay = (relativeAuctionTime.mul[relativeAuctionTime].mul[relativeAuctionTime]).div[decayDivisor] |
        			 price = ein._startPrice.mul[1.add[relativeAuctionTime]].div[(1.add[relativeAuctionTime]).add[decay]]
        //return price;
}*/

pred pre_bid[e:EstadoConcreto] {
	stateIs[e, Started]
	e._now > e._startTime
	e._now <= e._startTime.add[e._auctionDurationInDays]
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int, currentPrice: Int] {
	//PRE
	pre_bid[ein]
	//(some p:Int | currentPrice[ein, p] and value >= p)
	value >= currentPrice
	ein._whitelist[sender] = True
	//!isSenderContract()
	#ein._bidders < ein._maximalNumberOfParticipants
	ein._bids[sender] = 0

	//POST
	eout._bids = ein._bids++sender -> value
	eout._bidders = add[ein._bidders, sender]
	(//some p:Int | currentPrice[ein, p] and value >= p
		(currentPrice < ein._lowestSlotPrice) => eout._lowestSlotPrice = currentPrice
		else eout._lowestSlotPrice = ein._lowestSlotPrice
	)
        registerDepositor[ein, eout, sender, sender]
	
	(#eout._bidders = ein._maximalNumberOfParticipants) =>
		(eout._auctionState = DepositPending and eout._closeTime = ein._now)
	else
		(eout._auctionState = ein._auctionState and eout._closeTime = ein._closeTime)


	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	/*eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor*/
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
    	//eout._depositLocker = ein._depositLocker
    	eout._whitelist = ein._whitelist
	//eout._bids = ein._bids
    	//eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	//eout._closeTime = ein._closeTime
	//eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now.add[1] //lo agrego para simular el paso del tiempo
}

pred pre_startAuction[e:EstadoConcreto] {
	stateIs[e, Deployed]
	e._initialized[e._depositLocker] = True
}

pred met_startAuction[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int] {
	//PRE
	pre_startAuction[ein]

	//POST
        eout._auctionState = Started
        eout._startTime = ein._now

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
    	eout._depositLocker = ein._depositLocker
    	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
    	eout._bidders = ein._bidders
	//eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now.add[1] //lo agrego para simular el paso del tiempo
}

pred pre_depositBids[e:EstadoConcreto] {
	stateIs[e, DepositPending]
}

pred met_depositBids[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int] {
	//PRE
	pre_depositBids[ein]

	//POST
        eout._auctionState = Ended
//depositLocker.deposit.value(lowestSlotPrice * bidders.length)(lowestSlotPrice);
	deposit[ein, eout, sender, (ein._lowestSlotPrice.mul[#ein._bidders]), ein._lowestSlotPrice]
        
	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	/*eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor*/
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
    	eout._depositLocker = ein._depositLocker
    	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
    	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now.add[1] //lo agrego para simular el paso del tiempo
}

pred pre_closeAuction[e:EstadoConcreto] {
	stateIs[e, Started]
	e._now > e._startTime.add[e._auctionDurationInDays]
	#e._bidders < e._maximalNumberOfParticipants
}

pred met_closeAuction[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int] {
	//PRE
	pre_closeAuction[ein]

        (#ein._bidders >= ein._minimalNumberOfParticipants) =>
		transitionToDepositPending[ein, eout]
        else
            	transitionToAuctionFailed[ein, eout]

		//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
    	eout._depositLocker = ein._depositLocker
    	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
    	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	//eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now.add[1] //lo agrego para simular el paso del tiempo
}

pred pre_addToWhitelist[e:EstadoConcreto] {
	stateIs[e, Deployed]
}

pred met_addToWhitelist[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, addressesToWhitelist: seq Address] {
	//PRE
	pre_addToWhitelist[ein]
	onlyOwner[ein, sender]

	//POST
	(all a:Address| a in addressesToWhitelist.elems implies eout._whitelist[a] = True)
	(all a:Address| a !in addressesToWhitelist.elems and a in (ein._whitelist.Bool)
			implies eout._whitelist[a] = ein._whitelist[a])
	

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	eout._auctionState = ein._auctionState
    	eout._depositLocker = ein._depositLocker
    	//eout._whitelist = ein._whitelist
	eout._bids = ein._bids
    	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now.add[1] //lo agrego para simular el paso del tiempo
}

pred pre_withdraw[e:EstadoConcreto] {
	e._auctionState = Ended or e._auctionState = Failed
}

pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdraw[ein]
	
	//POST
	(ein._auctionState = Ended) =>
            withdrawAfterAuctionEnded[ein, eout,sender]
        else (ein._auctionState = Failed) =>
	   withdrawAfterAuctionFailed[ein, eout,sender]

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
    	eout._whitelist = ein._whitelist
	//eout._bids = ein._bids
    	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	//eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now.add[1] //lo agrego para simular el paso del tiempo
}


pred withdrawAfterAuctionEnded[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdrawAfterAuctionEnded[ein]
	ein._bids[sender] > ein._lowestSlotPrice
	ein._bids[sender].sub[ein._lowestSlotPrice] <= ein._bids[sender]

	//POST
	eout._bids[sender] = ein._lowestSlotPrice
        //msg.sender.transfer(valueToWithdraw);
}

pred pre_withdrawAfterAuctionEnded[e:EstadoConcreto] {
	stateIs[e, Ended]
}

pred withdrawAfterAuctionFailed[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	stateIs[ein, Failed]
	ein._bids[sender] > 0

	//POST
        //valueToWithdraw = bids[msg.sender];
        eout._bids[sender] = 0
        //msg.sender.transfer(valueToWithdraw);
}

pred pre_withdrawAfterAuctionFailed[e:EstadoConcreto] {
	stateIs[e, Failed]
}

pred transitionToDepositPending[ein: EstadoConcreto, eout: EstadoConcreto] {
	stateIs[ein, Started]

	eout._auctionState = DepositPending
	eout._closeTime = ein._now
}

pred transitionToAuctionFailed[ein: EstadoConcreto, eout: EstadoConcreto] {
	stateIs[ein, Started]

	eout._auctionState = Failed
	eout._closeTime = ein._now
}






//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._auctionState
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._auctionState = Deployed
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._auctionState = Started
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._auctionState = DepositPending
}

pred partitionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	e._auctionState = Ended
}

pred partitionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	e._auctionState = Failed
}

pred partitionINV[e:EstadoConcreto] {
	not invariante[e]
}










pred transicion_S00_a_S00_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S00_a_INV_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S01_a_S00_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S01_a_S01_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S01_a_S02_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S01_a_S03_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S01_a_S04_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S01_a_S05_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S01_a_INV_mediante_met_constructor{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S02_a_S00_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S02_a_S01_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S02_a_S02_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S02_a_S03_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S02_a_S04_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S02_a_S05_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S02_a_INV_mediante_met_constructor{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S03_a_S00_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S03_a_S01_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S03_a_S02_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S03_a_S03_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S03_a_S04_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S03_a_S05_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S03_a_INV_mediante_met_constructor{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S04_a_S00_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S04_a_S01_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S04_a_S02_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S04_a_S03_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S04_a_S04_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S04_a_S05_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S04_a_INV_mediante_met_constructor{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S05_a_S00_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S05_a_S01_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S05_a_S02_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S05_a_S03_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S05_a_S04_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S05_a_S05_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

pred transicion_S05_a_INV_mediante_met_constructor{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int, v30:DepositLocker | met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23, v30])
}

run transicion_S00_a_S00_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S03_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S04_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S05_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S00_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S01_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S02_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S03_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S04_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S05_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_INV_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S00_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S01_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S02_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S03_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S04_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S05_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_INV_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S00_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S01_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S02_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S03_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S04_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S05_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_INV_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S00_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S01_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S02_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S03_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S04_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S05_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_INV_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S00_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S01_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S02_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S03_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S04_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S05_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_INV_mediante_met_constructor for 2 EstadoConcreto, 3 DepositLocker
pred transicion_S00_a_S00_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S01_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S04_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S05_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_INV_mediante_met_bid{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S00_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S01_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S00_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S00_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S00_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S00_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S00_a_S00_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S01_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S02_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S03_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S04_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S05_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_INV_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S00_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S01_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S02_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S03_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S04_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S05_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_INV_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S00_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S01_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S02_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S03_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S04_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S05_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_INV_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S00_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S01_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S02_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S03_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S04_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S05_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_INV_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S00_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S01_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S02_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S03_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S04_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S05_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_INV_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S00_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S01_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S02_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S03_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S04_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S05_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_INV_mediante_met_bid for 2 EstadoConcreto, 3 DepositLocker
pred transicion_S00_a_S00_mediante_met_startAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_startAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_startAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_startAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_startAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_startAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_startAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_startAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_startAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_startAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_startAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_startAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_startAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_startAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_startAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_startAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_startAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_startAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_startAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_startAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_startAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_startAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_startAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_startAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_startAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_startAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_startAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_startAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S00_mediante_met_startAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_startAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_startAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_startAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_startAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_startAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_startAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S00_mediante_met_startAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_startAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_startAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_startAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_startAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_startAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_startAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_startAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S01_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S02_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S03_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S04_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S05_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_INV_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S00_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S01_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S02_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S03_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S04_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S05_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_INV_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S00_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S01_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S02_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S03_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S04_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S05_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_INV_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S00_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S01_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S02_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S03_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S04_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S05_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_INV_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S00_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S01_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S02_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S03_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S04_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S05_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_INV_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S00_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S01_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S02_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S03_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S04_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S05_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_INV_mediante_met_startAuction for 2 EstadoConcreto, 3 DepositLocker
pred transicion_S00_a_S00_mediante_met_depositBids{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_depositBids{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_depositBids{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_depositBids{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_depositBids{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_depositBids{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_depositBids{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_depositBids{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_depositBids{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_depositBids{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_depositBids{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_depositBids{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_depositBids{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_depositBids{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_depositBids{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_depositBids{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_depositBids{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_depositBids{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_depositBids{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_depositBids{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_depositBids{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_depositBids{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_depositBids{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_depositBids{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_depositBids{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_depositBids{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_depositBids{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_depositBids{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S00_mediante_met_depositBids{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_depositBids{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_depositBids{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_depositBids{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_depositBids{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_depositBids{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_depositBids{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S00_mediante_met_depositBids{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_depositBids{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_depositBids{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_depositBids{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_depositBids{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_depositBids{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_depositBids{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_depositBids [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S01_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S02_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S03_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S04_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S05_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_INV_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S00_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S01_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S02_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S03_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S04_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S05_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_INV_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S00_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S01_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S02_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S03_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S04_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S05_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_INV_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S00_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S01_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S02_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S03_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S04_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S05_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_INV_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S00_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S01_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S02_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S03_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S04_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S05_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_INV_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S00_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S01_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S02_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S03_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S04_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S05_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_INV_mediante_met_depositBids for 2 EstadoConcreto, 3 DepositLocker
pred transicion_S00_a_S00_mediante_met_closeAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_closeAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_closeAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_closeAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_closeAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_closeAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_closeAuction{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_closeAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_closeAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_closeAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_closeAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_closeAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_closeAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_closeAuction{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_closeAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_closeAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_closeAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_closeAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_closeAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_closeAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_closeAuction{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_closeAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_closeAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_closeAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_closeAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_closeAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_closeAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_closeAuction{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S00_mediante_met_closeAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_closeAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_closeAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_closeAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_closeAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_closeAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_closeAuction{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S00_mediante_met_closeAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_closeAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_closeAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_closeAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_closeAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_closeAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_closeAuction{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | met_closeAuction [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S01_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S02_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S03_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S04_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S05_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_INV_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S00_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S01_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S02_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S03_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S04_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S05_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_INV_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S00_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S01_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S02_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S03_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S04_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S05_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_INV_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S00_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S01_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S02_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S03_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S04_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S05_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_INV_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S00_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S01_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S02_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S03_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S04_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S05_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_INV_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S00_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S01_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S02_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S03_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S04_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S05_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_INV_mediante_met_closeAuction for 2 EstadoConcreto, 3 DepositLocker
pred transicion_S00_a_S00_mediante_met_addToWhitelist{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S01_mediante_met_addToWhitelist{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_addToWhitelist{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_addToWhitelist{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_addToWhitelist{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_addToWhitelist{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_addToWhitelist{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S00_mediante_met_addToWhitelist{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S01_mediante_met_addToWhitelist{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_addToWhitelist{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_addToWhitelist{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_addToWhitelist{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_addToWhitelist{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_addToWhitelist{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S00_mediante_met_addToWhitelist{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_addToWhitelist{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_addToWhitelist{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_addToWhitelist{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_addToWhitelist{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_addToWhitelist{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_addToWhitelist{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S00_mediante_met_addToWhitelist{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_addToWhitelist{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_addToWhitelist{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_addToWhitelist{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_addToWhitelist{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_addToWhitelist{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_addToWhitelist{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S00_mediante_met_addToWhitelist{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_addToWhitelist{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_addToWhitelist{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_addToWhitelist{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_addToWhitelist{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_addToWhitelist{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_addToWhitelist{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S00_mediante_met_addToWhitelist{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_addToWhitelist{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_addToWhitelist{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_addToWhitelist{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_addToWhitelist{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_addToWhitelist{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_addToWhitelist{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:seq Address | met_addToWhitelist [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S00_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S01_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S02_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S03_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S04_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S05_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_INV_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S00_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S01_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S02_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S03_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S04_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S05_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_INV_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S00_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S01_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S02_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S03_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S04_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S05_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_INV_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S00_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S01_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S02_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S03_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S04_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S05_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_INV_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S00_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S01_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S02_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S03_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S04_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S05_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_INV_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S00_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S01_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S02_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S03_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S04_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S05_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_INV_mediante_met_addToWhitelist for 2 EstadoConcreto, 3 DepositLocker
pred transicion_S00_a_S00_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S01_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S02_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S03_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S04_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_S05_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S00_a_INV_mediante_met_withdraw{
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S00_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S01_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_INV_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S00_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_INV_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S00_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_INV_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S00_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_INV_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S00_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS00[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_INV_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address | met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S00_a_S00_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S01_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S02_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S03_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S04_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_S05_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S00_a_INV_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S00_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S01_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S02_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S03_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S04_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_S05_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S01_a_INV_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S00_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S01_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S02_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S03_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S04_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_S05_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S02_a_INV_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S00_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S01_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S02_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S03_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S04_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_S05_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S03_a_INV_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S00_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S01_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S02_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S03_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S04_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_S05_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S04_a_INV_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S00_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S01_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S02_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S03_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S04_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_S05_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
run transicion_S05_a_INV_mediante_met_withdraw for 2 EstadoConcreto, 3 DepositLocker
