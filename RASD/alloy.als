// ================================================================================================
// ======================== PRIMITIVE SIGNATURES
sig Name {}

sig Surname {}

sig Email {}

sig Address {}

sig Double {}

enum Bool {
	True,
	False
	}

// ================================================================================================
// ======================== SIGNATURES
sig Time {
	value: Int
	} { value >= 0 }

sig Date {
	value: Int
	} { value >= 0 }

sig Ride {
	makeUseTicket: lone Ticket,
	byTranMean: TransportationMean,
	fromLocation: Location,
	toLocation: Location
	}	{ fromLocation != toLocation }

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
	hasPreferences: Preferences,
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
	} { every > 0 
		   start.value < end.value }

sig TravelPlan {
	passengers: Int,
	baggage: Int,
	startRide: Ride,
	intermediateRides: set Ride,
	endRide: Ride,
	forAppointment: Appointment
	} {
			passengers >= 0
			baggage >= 0
			no is: intermediateRides | startRide = is or endRide = is
			lone is: intermediateRides | startRide.toLocation = is.fromLocation
			lone is: intermediateRides | endRide.fromLocation = is.toLocation
			no is: intermediateRides | startRide.fromLocation = is.toLocation
			no is: intermediateRides | endRide.toLocation = is.fromLocation
			all is: intermediateRides | is.toLocation = endRide.fromLocation or 
				one is1: intermediateRides | is.toLocation = is1.fromLocation
			all is: intermediateRides | is.fromLocation = startRide.toLocation or
				one is1: intermediateRides | is.fromLocation = is1.toLocation	
			#intermediateRides = 0 implies 
				(startRide = endRide or startRide.toLocation = endRide.fromLocation)		
		}

fun travelPlanRides [t: TravelPlan] : some Ride {
	t.startRide + t.intermediateRides + t.endRide
}

abstract sig BreakWindow {}

sig FixedBreakWindow extends BreakWindow {
	from: Time,
	to: Time
	} { from.value < to.value }

sig FlexibleBreakWindow extends BreakWindow {
	from: Time,
	to: Time,
	atLeast: Time
	} { from.value < to.value
		  (atLeast.value > 0 and atLeast.value < minus[to.@value, from.@value]) }

enum Language {
	Italiano,
	English,
	Francais
	}

abstract sig TransportationMean {
	belongsToCompany: lone TransportationCompany
	}

one sig Foot, MoBike, PersonalCar, EnjoyCar, Metro, Tram extends TransportationMean {}

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
	} { fromValue >= 0
		  toValue >= 0
		  fromValue < toValue }

sig TimeWindowConstraint extends TransportationMeanConstraint{
	from: Time,
	to: Time
	} { from.value < to.value }

// ================================================================================================
// ======================== ADDITIONAL SIGNATURES
sig SuggestedSolutions {
	suggestTo: User,
	containsSolutions: some Solution
	}

sig Solution {
	suggestTranMean: some TransportationMean,
	forAppointment: Appointment,	
	}

sig Device {
	belongsTo: User,
	language: Language
}

sig AppInstance{
	installedOn: Device,
	displayLanguage: Language
}{ let d = installedOn | (displayLanguage = d.language) or
			(displayLanguage = English and d.language not in SupportedLanguages.setOfLanguages) }

one sig SupportedLanguages {
	setOfLanguages: set Language
}

// ================================================================================================
// ======================== FACTS
fact EmailsAreUnique {
	all disjoint u1, u2: User | u1.email != u2.email 
	}

fact NoOverlappingLocations {
	all disjoint l1, l2: Location | (l1.latitude != l2.latitude) || (l1.longitude != l2.longitude)
	}

fact TimeIsUnique {
	all disjoint t1, t2: Time | t1.value != t2.value
	}

fact ATicketBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.ownsTicket & u2.ownsTicket = none
	}

fact TicketMustBelongToUsers {
	all t: Ticket | some u: User | t in u.ownsTicket
	}

fact TicketMustBeAssociatedToRides {
	all t: Ticket | some r: Ride | t in r.makeUseTicket
	}

fact APreferenceBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.hasPreferences & u2.hasPreferences = none
	}

fact TranMeanConstraintsRefersOnlyToOneUser {
	all disjoint u1, u2: User | u1.hasConstraints & u2.hasConstraints = none
	}

fact ABreakWindowIsSetOnlyByOneUser {
	all disjoint u1, u2: User | u1.setBreakWindows & u2.setBreakWindows = none
	}

fact AnAppointmentIsCreatedOnlyByOneUser {
	all disjoint u1, u2: User | u1.createsAppointment & u2.createsAppointment = none
	}

fact AppointmentsMustBeCreatedOnlyByUsers {
	all a: Appointment | some u: User | a in u.createsAppointment
	}

fact ATravelPlanBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.hasTravelPlan & u2.hasTravelPlan = none
	}

fact DisabledTranMeansAreNotSuggested {
	all p: Preferences, s: SuggestedSolutions, u: User |
	p in u.hasPreferences and
	s.suggestTo = u and
	u.hasPreferences.disabledTranMean & (s.containsSolutions).suggestTranMean = none
	}

// if an appointment is associated to a user travel plan, the user must partecipate to the appointment
fact ConsistentUserTravelPlanAppointment { 
	all u: User, a: Appointment, tp: TravelPlan | 
	(tp.forAppointment = a and tp in u.hasTravelPlan) implies (a in u.partecipatesToAppointment)
	}

fact AppointmentCreationImpliesPartecipation {
	all u: User, a: Appointment | 
	(a in u.createsAppointment) implies (a in u.partecipatesToAppointment)
	}

// there is not the possibility to have a name, surname, email, address, appointment
//  type or transportation company without associations with something
fact NameMustBelongToUsers {
	all n: Name | some u: User | u.name = n
	}

fact SurnameMustBelongToUsers {
	all s: Surname | some u: User | u.surname = s
	}

fact EmailMustBelongToUsers {
	all e: Email | some u: User | u.email = e
	}

fact AddressMustBelongToLocations {
	all a: Address | some loc: Location | loc.address = a
	}

fact AppointmentTypeMustBeAssociatedToAppointments {
	all at: AppointmentType | some a: Appointment | a.hasType = at
	}

fact TranCompanyMustBeAssociatedWithTicketOrTranMean {
	all tc: TransportationCompany | some t: Ticket, tm: TransportationMean | 
	(t.providedByCompany = tc or tm.belongsToCompany = tc)
	}

// No tickets for personal and shared transportation means
fact TicketsUsedOnlyIfNecessary {
	all t: Ticket | (Foot & t.usedFor = none) and
	(MoBike & t.usedFor = none) and 
	(PersonalCar & t.usedFor = none) and
	(EnjoyCar & t.usedFor = none)
	}

fact NoTranCompanyForPersonalTranMeans  {
	(Foot.belongsToCompany = none) and
	(PersonalCar.belongsToCompany= none)
	}

fact TranMeanConstraintsMustBelongToUsers {
	all tmc: TransportationMeanConstraint | some u: User | tmc in u.hasConstraints 
	}

fact BreakWindowMustBeSetByUsers {
	all bw: BreakWindow | some u: User | bw in u.setBreakWindows
	}

fact RideMustBelongToTravelPlans {
	all r: Ride | some tp: TravelPlan | r in travelPlanRides[tp]
	}

fact RideBelongsToOnlyOneTravelPlan {
	all disjoint tp1, tp2: TravelPlan | travelPlanRides[tp1] & travelPlanRides[tp2] = none
}

fact TravelPlanMustBelongToUsers {
	all tp: TravelPlan | some u: User | tp in u.hasTravelPlan
	}

fact SolutionMustBeSuggested {
	all s: Solution | some ss: SuggestedSolutions | s in ss.containsSolutions
	}

fact LocationAssociatedToRideAppointmentOrUser {
	all l: Location | some r: Ride, a: Appointment, u: User |
	l in (r.fromLocation + r.toLocation + a.atLocation + u.currentlyAtLoc)
	}

fact RepeatableAppointmentIsAnAppointment {
	all ra: RepeatableAppointment | some a: Appointment | ra in a.isRepeatable
	}

fact RepeatableAppointmentsAtTheSameTime {
	all a1, a2: Appointment | (a1.isRepeatable = a2.isRepeatable) implies  
	(a1.start = a2.start and a1.end = a2.end)
	}

fact NoStartRideFromAppointmentLocation {
	all tp: TravelPlan | tp.startRide.fromLocation != tp.forAppointment.atLocation
	}

// ================================================================================================
// ======================== ASSERTIONS
assert CanDisplayInAllSupportedLanguages {
	no l: AppInstance.installedOn.language |
		l in SupportedLanguages.setOfLanguages and
		no ap: AppInstance | ap.displayLanguage = l
}

check CanDisplayInAllSupportedLanguages
	
pred show {}

run show 

