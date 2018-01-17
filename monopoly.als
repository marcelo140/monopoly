open util/integer

sig Color {}

sig Property {
	color: lone Color
}

sig Player {
	properties: set Property,
	houses: Property -> House
}

abstract sig Building {}

sig Hotel extends Building {}

sig House extends Building {}

fact properties_are_own_by_at_most_one_player {
	properties in Player lone -> Property
}

fact houses_are_own_by_at_most_one_property {
	Player.houses in Property lone -> House
}

fact only_properties_with_color_can_have_houses {
	all h: House | one h.~(Player.houses).color
}

fact player_has_houses_only_if_owns_all_properties_of_that_color {
	all p: Player, cs: p.houses.House.color |
		cs.~color in p.properties
}

fact properties_have_similar_number_of_houses {
	all p: Color.~color |
		all other: p.color.~color - p |
			lte[minus[#(p.(Player.houses)), #(other.(Player.houses))], 1]
				and 
			lte[minus[#(other.(Player.houses)), #(p.(Player.houses))], 1]
}

run {}
