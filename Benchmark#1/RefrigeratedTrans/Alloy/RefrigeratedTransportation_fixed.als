// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{transiciones: Accion -> set EstadoAbstracto}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


//Acciones de los estados abstractos
abstract sig Accion{}
one sig AccionConstructor extends Accion {}
one sig AccionIngestTelemetry extends Accion {}
one sig AccionTransferResponsibility extends Accion {}
one sig AccionComplete extends Accion {}

// Describo cómo pasar de un estado a otro mediante cada acción
fact trans_accionConstructor{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionConstructor]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10,v11,v12,v13:Address/*,v20,v21,v22,v23:Int*/ | constructor[e0,e1,v10,v11,v12,v13/*,v20,v21,v22,v23*/]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionIngestTelemetry{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionIngestTelemetry]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20,v21,v22:Int | ingestTelemetry[e0,e1,v10,v20,v21,v22]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionTransferResponsibility{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionTransferResponsibility]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10,v11:Address | transferResponsibility[e0,e1,v10,v11]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionComplete{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionComplete]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | complete[e0,e1,v10]
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
one sig Created extends EstadoContrato{}
one sig InTransit extends EstadoContrato{}
one sig Completed extends EstadoContrato{}
one sig OutOfCompliance extends EstadoContrato{}

abstract sig SensorType{}
one sig None extends SensorType{}
one sig Humidity extends SensorType{}
one sig Temperature extends SensorType{}

//Boolean sólo puede ser True o False

abstract sig Boolean{}
one sig True extends Boolean{}
one sig False extends Boolean{}

abstract sig EstadoConcreto {
	_owner: lone Address,
	_initiatingCounterparty: lone Address,
	_counterparty: lone Address,
	_previousCounterparty: lone Address,
	_device: lone Address,
	_supplyChainOwner: lone Address,
	_supplyChainObserver: lone Address,
	_minHumidity: lone Int,
	_maxHumidity: lone Int,
	_minTemperature: lone Int,
	_maxTemperature: lone Int,
	_complianceSensorType: lone SensorType,
	_complianceSensorReading: lone Int,
	_complianceStatus: lone Boolean,
	_complianceDetail: lone Texto,
	_lastSensorUpdateTimestamp: lone Int,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


//fact {all x: Int | x > 0}

pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	(no disj a1,a2:Address | a1.name = a2.name)
}

pred constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, device: Address, supplyChainOwner: Address,
		supplyChainObserver: Address/*, minHumidity: Int, maxHumidity: Int, minTemperature: Int,
		maxTemperature: Int*/] {
	//Pre
	no ein._state and no _previousCounterparty and no _complianceSensorType and no ein._lastSensorUpdateTimestamp
	no ein._complianceStatus and no ein._complianceSensorReading and no ein._complianceSensorReading
	no ein._owner and no ein._counterparty and no ein._initiatingCounterparty and no ein._device
	no ein._supplyChainOwner and no ein._supplyChainObserver and no ein._minHumidity
	no ein._maxHumidity and no ein._minTemperature and no ein._maxTemperature and no ein._complianceDetail
	//Post
        eout._complianceStatus = True
        eout._complianceSensorReading = -1
        eout._initiatingCounterparty = sender
        eout._owner = eout._initiatingCounterparty
        eout._counterparty = eout._initiatingCounterparty
        eout._device = device
        eout._supplyChainOwner = supplyChainOwner
        eout._supplyChainObserver = supplyChainObserver
        eout._minHumidity = -4
        eout._maxHumidity = 7
        eout._minTemperature = -4
        eout._maxTemperature = 7
        eout._state = Created
        eout._complianceDetail = TextoA
	eout._previousCounterparty = ein._previousCounterparty
	eout._complianceSensorType = ein._complianceSensorType
	eout._lastSensorUpdateTimestamp = ein._lastSensorUpdateTimestamp
}

pred ingestTelemetry[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, humidity: Int,
			temperature: Int, timestamp: Int] {
	//Pre
	some ein._state
	ein._state != Completed and ein._state != OutOfCompliance and ein._device = sender

	//Post
        	eout._lastSensorUpdateTimestamp = timestamp
        (humidity > ein._maxHumidity or humidity < ein._minHumidity) =>
		(
	            eout._complianceSensorType = Humidity and 
	            eout._complianceSensorReading = humidity and
	            eout._complianceDetail = TextoB and 
	            eout._complianceStatus = False
		)
	else
		(
			(temperature > ein._maxTemperature or temperature < ein._minTemperature)
				=> (
						eout._complianceSensorType = Temperature and
					         eout._complianceSensorReading = temperature and
					         eout._complianceDetail = TextoC and
					         eout._complianceStatus = False
				     )
				else  (
						eout._complianceSensorType = ein._complianceSensorType and
					         eout._complianceSensorReading = ein._complianceSensorReading and
					         eout._complianceDetail = ein._complianceDetail and
					         eout._complianceStatus = ein._complianceStatus
					)
		)

        (ein._complianceStatus = False) => (eout._state = OutOfCompliance) else eout._state = ein._state
        eout._initiatingCounterparty = ein._initiatingCounterparty
        eout._owner = ein._owner
        eout._counterparty = ein._counterparty
        eout._device = ein._device
        eout._supplyChainOwner = ein._supplyChainOwner
        eout._supplyChainObserver = ein._supplyChainObserver
        eout._minHumidity = ein._minHumidity
        eout._maxHumidity = ein._maxHumidity
        eout._minTemperature = ein._minTemperature
	eout._maxTemperature = ein._maxTemperature
	eout._previousCounterparty = ein._previousCounterparty
    }

pred transferResponsibility[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, newCounterparty: Address] {
        //Pre
	some ein._state
	(ein._state != Completed and ein._state != OutOfCompliance)
	(ein._initiatingCounterparty = sender or ein._counterparty = sender)
	(newCounterparty != ein._device)

	//Post
	ein._state = Created => eout._state = InTransit else eout._state = ein._state
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = newCounterparty

	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._owner = ein._owner
	eout._device = ein._device
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
	eout._minHumidity = ein._minHumidity
	eout._maxHumidity = ein._maxHumidity
	eout._minTemperature = ein._minTemperature
	eout._maxTemperature = ein._maxTemperature
	eout._complianceSensorType = ein._complianceSensorType
	eout._complianceSensorReading = ein._complianceSensorReading
	eout._complianceDetail = ein._complianceDetail
	eout._complianceStatus = ein._complianceStatus
	eout._lastSensorUpdateTimestamp = ein._lastSensorUpdateTimestamp
}

pred complete[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	some ein._state
	ein._state != Completed and ein._state != OutOfCompliance
	ein._state != Created //agrego FIX
	ein._owner = sender or ein._supplyChainOwner = sender
	//Post
	eout._state = Completed
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = Address0

	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._owner = ein._owner
	eout._device = ein._device
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
	eout._minHumidity = ein._minHumidity
	eout._maxHumidity = ein._maxHumidity
	eout._minTemperature = ein._minTemperature
	eout._maxTemperature = ein._maxTemperature
	eout._complianceSensorType = ein._complianceSensorType
	eout._complianceSensorReading = ein._complianceSensorReading
	eout._complianceDetail = ein._complianceDetail
	eout._complianceStatus = ein._complianceStatus
	eout._lastSensorUpdateTimestamp = ein._lastSensorUpdateTimestamp
}

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

pred particionS4[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = OutOfCompliance
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

pred transicion_S0_a_S4_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S1_a_S4_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S2_a_S4_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S3_a_S4_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S3_a_IN_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S4_a_S4_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS4[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S4_a_S0_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S4_a_S1_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S4_a_S2_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S4_a_S3_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S4_a_IN_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


run transicion_S0_a_S0_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S1_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S2_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S3_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S4_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S0_a_IN_mediante_constructor for 2 EstadoConcreto, 5 Address

run transicion_S1_a_S1_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S0_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S2_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S3_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S4_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S1_a_IN_mediante_constructor for 2 EstadoConcreto, 5 Address

run transicion_S2_a_S2_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S0_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S1_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S3_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S4_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S2_a_IN_mediante_constructor for 2 EstadoConcreto, 5 Address

run transicion_S3_a_S3_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S0_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S1_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S2_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S4_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S3_a_IN_mediante_constructor for 2 EstadoConcreto, 5 Address

run transicion_S4_a_S4_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S0_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S1_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S2_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S3_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S4_a_IN_mediante_constructor for 2 EstadoConcreto, 5 Address

pred transicion_S0_a_S0_mediante_ingestTelemetry{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS0[e]))
	(A0 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S0_a_S1_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S0_a_S2_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S0_a_S3_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S0_a_S4_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S0_a_IN_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}


pred transicion_S1_a_S1_mediante_ingestTelemetry{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS1[e]))
	(A0 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S1_a_S0_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S1_a_S2_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S1_a_S3_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S1_a_S4_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S1_a_IN_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}


pred transicion_S2_a_S2_mediante_ingestTelemetry{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS2[e]))
	(A0 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S2_a_S0_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S2_a_S1_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S2_a_S3_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S2_a_S4_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S2_a_IN_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}


pred transicion_S3_a_S3_mediante_ingestTelemetry{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS3[e]))
	(A0 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S3_a_S0_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S3_a_S1_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S3_a_S2_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S3_a_S4_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S3_a_IN_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}


pred transicion_S4_a_S4_mediante_ingestTelemetry{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS4[e]))
	(A0 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S4_a_S0_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S4_a_S1_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S4_a_S2_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S4_a_S3_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}

pred transicion_S4_a_IN_mediante_ingestTelemetry{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionIngestTelemetry])
}


run transicion_S0_a_S0_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S1_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S2_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S3_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S4_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S0_a_IN_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address

run transicion_S1_a_S1_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S0_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S2_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S3_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S4_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S1_a_IN_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address

run transicion_S2_a_S2_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S0_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S1_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S3_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S4_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S2_a_IN_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address

run transicion_S3_a_S3_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S0_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S1_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S2_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S4_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S3_a_IN_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address

run transicion_S4_a_S4_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S0_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S1_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S2_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S3_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address
run transicion_S4_a_IN_mediante_ingestTelemetry for 2 EstadoConcreto, 5 Address

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

pred transicion_S0_a_S4_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S1_a_S4_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S2_a_S4_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S3_a_S4_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S3_a_IN_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}


pred transicion_S4_a_S4_mediante_transferResponsibility{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS4[e]))
	(A0 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S4_a_S0_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S4_a_S1_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S4_a_S2_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S4_a_S3_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}

pred transicion_S4_a_IN_mediante_transferResponsibility{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionTransferResponsibility])
}


run transicion_S0_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S4_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S0_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address

run transicion_S1_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S4_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S1_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address

run transicion_S2_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S4_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S2_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address

run transicion_S3_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S4_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S3_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address

run transicion_S4_a_S4_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S0_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S1_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S2_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S3_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address
run transicion_S4_a_IN_mediante_transferResponsibility for 2 EstadoConcreto, 5 Address

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

pred transicion_S0_a_S4_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS0[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S1_a_S4_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS1[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S2_a_S4_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS2[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
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

pred transicion_S3_a_S4_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS4[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S3_a_IN_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS3[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}


pred transicion_S4_a_S4_mediante_complete{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS4[e]))
	(A0 in A0.transiciones[AccionComplete])
}

pred transicion_S4_a_S0_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS0[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S4_a_S1_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS1[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S4_a_S2_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS2[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S4_a_S3_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS3[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}

pred transicion_S4_a_IN_mediante_complete{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS4[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionIN[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionComplete])
}


run transicion_S0_a_S0_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S1_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S2_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S3_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S0_a_S4_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S0_a_IN_mediante_complete for 2 EstadoConcreto, 5 Address

run transicion_S1_a_S1_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S0_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S2_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S3_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S1_a_S4_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S1_a_IN_mediante_complete for 2 EstadoConcreto, 5 Address

run transicion_S2_a_S2_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S0_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S1_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S3_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S2_a_S4_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S2_a_IN_mediante_complete for 2 EstadoConcreto, 5 Address

run transicion_S3_a_S3_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S0_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S1_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S2_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S3_a_S4_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S3_a_IN_mediante_complete for 2 EstadoConcreto, 5 Address

run transicion_S4_a_S4_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S0_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S1_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S2_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S4_a_S3_mediante_complete for 2 EstadoConcreto, 5 Address
run transicion_S4_a_IN_mediante_complete for 2 EstadoConcreto, 5 Address
