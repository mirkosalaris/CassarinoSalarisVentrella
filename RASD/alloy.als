//primitive signatures 
sig Name {}

sig Surname {}

sig Email {}

sig Address {}

sig Double {}

sig Time {}

sig Date {}

enum Bool {
	True,
	False
	}

//signatures
sig Ride {
	makeUseTicket: lone Ticket,
	byTranMean: TransportationMean,
	fromLocation: Location,
	toLocation: Location
	}	

sig TransportationCompany {}

abstract sig Ticket {
	usedFor: some TransportationMean,
	providedByCompany: TransportationCompany
	}

sig User {
	name: Name,
	surname: Surname,
	email: Email,
	ownsTicket: set Ticket,
	setPreferences: Preferences,
	hasConstraints: set TransportationMeanConstraint,
	speaksLanguage: Language,
	setBreakWindows: set BreakWindow,
	createsAppointment: set Appointment,
	partecipatesToAppointment: set Appointment,
	hasTravelPlan: set TravelPlan,
	currentlyAtLoc: Location
	}

sig Appointment {
	start: Time,
	end: Time, 
	atLocation: Location,
	hasType: AppointmentType,
	isRepeatable: lone RepeatableAppointment
	}

sig Location {
	address: Address,
	latitude: Double,
	longitude: Double
	}

enum AppointmentType {
	Personal,
	Work
	}

sig RepeatableAppointment {
	every: Int,
	start: Date, 
	end: Date
	}

sig TravelPlan {
	passengers: Int,
	baggages: Int,
	hasRide: some Ride,
	forAppointment: Appointment
	}

abstract sig BreakWindow {}

sig FixedBreakWindow extends BreakWindow {
	from: Time,
	to: Time
	}

sig FlexibleBreakWindow extends BreakWindow {
	from: Time,
	to: Time,
	atLeast: Time
	}

enum Language {
	Italiano,
	English,
	Francais
	}

abstract sig TransportationMean {
	belongsToCompany: TransportationCompany
	}

one sig Foot, Car, Taxi, Metro, Tram extends TransportationMean {}

sig Preferences {
	ecoFriendly: Bool,
	disabledTranMean: set TransportationMean
	}

abstract sig TransportationMeanConstraint {
	associatedToTranMean: TransportationMean
	}

sig DistanceConstraint extends TransportationMeanConstraint { 
	fromValue: Int,
	toValue: Int
	}

sig TimeWindowConstraint extends TransportationMeanConstraint{
	from: Time,
	to: Time
	}


pred show {}

run show


