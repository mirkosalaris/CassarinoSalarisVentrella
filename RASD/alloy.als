abstract sig Ride {
	makeUse: lone Ticket,
	associatedWith: TransportationMean
	}	

abstract sig PersonalRide extends Ride {}

abstract sig CompanyCustomRide {}

abstract sig Ticket {
	usedFor: some TransportationMean
	}

sig User {
	name: String,
	surname: String,
	email: String,
	ownsTicket: set Ticket,
	setPreferences: Preferences,
	hasConstraints: set TransportationMeanConstraint,
	speaksLanguage: Language,
	setBreakWindows: BreakWindow,
	createsAppointment: set Appointment,
	partecipatesToAppointment: set Appointment,
	hasTravelPlan: set TravelPlan
	}

sig Appointment {
	start: Time,
	end: Time, 
	atLocation: Location,
	hasType: AppointmentType,
	isRepeatable: lone RepeatableAppointment
	}

sig Location {
	address: String,
	latitude: Int,
	longitude: Int
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
	hasConstraint: set TransportationMeanConstraint
	}

one sig Foot, Car, Taxi, Metro, Tram extends TransportationMean {}

sig Preferences {
	ecoFriendly: Bool,
	disabledTranMean: set TransportattionMean
	}

abstract sig TransportationMeanConstraint {}

sig DistanceConstraint extends TransportationMeanConstraint {
	value: Int,
	minMax: Bool
	}

sig TimeWindowConstraint {
	from: Time,
	to: Time
	}


