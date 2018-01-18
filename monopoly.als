open util/integer

sig Color {}

sig Property {
	color: lone Color
}

sig Player {
	properties: set Property,
	houses: Property -> set House,
	hotels: Property -> lone Hotel
}

abstract sig Building {}

sig Hotel extends Building {}

sig House extends Building {}

fact properties_are_own_by_at_most_one_player {
	properties in Player lone -> Property
}

fact buildings_are_own_by_at_most_one_property {
	Player.houses + Player.hotels in Property lone -> Building
}

fact only_properties_with_color_can_have_houses {
	all b: Building | one b.~(Player.(houses+hotels)).color
}

fact player_has_houses_only_if_owns_all_properties_of_that_color {
	all p: Player, cs: p.(houses+hotels).Building.color |
		cs.~color in p.properties
}

fact properties_have_similar_number_of_houses {
	all p: Color.~color | all other: p.color.~color - p {
		no (p+other).(Player.hotels) => lte[minus[#(p.(Player.houses)), #(other.(Player.houses))], 1]

		some p.(Player.hotels) => some other.(Player.hotels) or gte[#(other.(Player.houses)), 3]
	}
}

fact no_more_than_4_houses {
	all p: Property |	lte[#(p.(Player.houses)), 4]
}

fact properties_with_hotel_have_no_houses {
	all p:Property | some p.(Player.hotels) => no p.(Player.houses)
}

run {}
