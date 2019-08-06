// OK!!!! What menu of options do we want for the visualization? That's second priority.

/*
colors for nodes and edges
name changes?
font size
hiding/showing
box types / line types
show relaitons as attributes
numbering nodes?
line weights
layout options: force, arcing edges, separations?

function options for these where available.
how to represent hyper edges
compound areas?
projection type things? graph changes.

I can organize these into two types of styling:
graph changes, and style changes.
graph changes are more complex, and will require more thought, definitely.


graph is moving back to starting position when you tab to another tab and back,
that's on list to fix.

multiple runs are screwed up, and cytoscape isn't fitting things correctly.

plan: minimal documentation on presentation and manipulation, then styling work.
Can honestly just put a link to the html for the documentation in the thing, that would be
even better i think.

ALSO: unsat behavior!!!!



engineering debt! highest priority
different colored edges (eh?)
expanding instance into visualizer: you evaluate some expression, and check some box, to expand instance
you can add a relation. Evaluating a predicate is weirder, so don't do that for now.
removing relations.
optional zooming, font size in evaluator, maybe hiding and showing
relations as attributes? projections?
projection is just for state, remember. so not yet.
relations as attributes is low priority, but do want it as base functionality.
saved theming would be nice for later, file based

using kodkod to evaluate instead of doing it ourselves


we really really need logging from each layer! that's part of the engineering debt.
and we need good errors / error propagation. also part of engineering debt
check relation arities before running! those should prob be part of ast.
focus should be on ocelot, cuz we should really really trust kodkod.


evaluator really important, used in class

*/

// OK, what's the most basic styling I can start with?
// Color, adjust the color.

// How? Need a menu thing there... what? and where?
// Do it on top of the model, that's easy.
// so put a div there.
//



// how to do more complicated layouts? I think compound nodes are the answer.
// make a compound node containing all state atoms, for instance, and then it's way easier to lay out.
// Hmmm, but how extensible is that. because each node can only have one parent...
// I guess if we want to lay out some groups differently, we just don't apply the layout to them, but only to a
// compound node parent containing all of them, and then lay them out individually. Yeah, that works fine.

// more important: unique colors for each relation of arity > 1!
// Is that super important though? Cleaning up other stuff might be more important...
// I'm exhausted. Think about this later.


var nodes = json.nodes.map(function(name){
	return {
		data: {
			id: name,
			label: name,
			color: "#666"
		}
	}
});

var edges = Object.entries(json.relations).reduce(function(acc, val){
	relation_name = val[0];

	return acc.concat(val[1].map(function(tuple){
		console.assert(tuple.length >= 1);

		var start = tuple[0];
		var end = tuple[tuple.length - 1];

		var label = relation_name + "\n\n\u2060";
		if (tuple.length > 2){
			var between = tuple.slice(1, tuple.length - 1);
			label = relation_name + "[" + between.join("->") + "]\n\n.";
		}

		return {
			data: {
				id: tuple.join(),
				source: start,
				target: end,
				label: label,
				color: "#ccc"
			}
		}
	}));
}, []);

//function edges_equal(edgeA, edgeB){

//}

//notseen = function(edge, index, self){
//	return self.indexOf(edge)
//}

var cy = cytoscape({

	container: document.getElementById('cy'), // container to render in

	elements: nodes.concat(edges),

	style: [ // the stylesheet for the graph
		{
			selector: 'node',
			style: {
				'background-color': 'yellow',
				'label': 'data(id)',
				'font-size': 12,
				'color': 'data(color)',
				'shape': 'barrel',
				'width': 100,
				'border-color': 'black',
				'border-width': 2,
				'text-valign': 'center',
				'text-halign': 'center'
			}
		},

		{
			selector: 'edge',
			style: {
			 	'width': 3,
				'line-color': "data(color)",
				'target-arrow-color': 'data(color)',
				'target-arrow-shape': 'triangle',
				'curve-style': 'bezier',
				'label': 'data(label)',
				'text-wrap': 'wrap',
				'control-point-weight': 0.8,
				'control-point-step-size': 50,
				'font-size': 12,
				'color': 'data(color)',
				"edge-text-rotation": "autorotate"
			}
		}
	],

	// gotta use bezier, definitely.
	// control point step size
	// control point weight
	// avsdf layout?

	layout: {
		//name: 'cose-bilkent'
		name: "circle"
		// rows: 6
	},

	userZoomingEnabled: false
	// layout: {
	// 	name: "cose"
	// }

});


// THATS THE PRBLEM IT CANT HAVE DUPLICATE EDGES. THIS CONTAINS DUPLICATE EDGES
// no, it's not that. It's not that. cose-bilkent must be broken, that's the real problem.

// yeah, having all four edges in there causes the internal this.nodes to become empty.
// which makes no sense and shouldn't happen ever.
// so use a different layout.

// var cy = cytoscape({
// 	container: document.getElementById('cy'),
// 	elements: nodes.concat([edges[4], edges[5], edges[6], edges[7]]),
// 	style: [
// 		{
// 			selector: 'node',
// 			style: {
// 				'width': 100
// 			}
// 		},
// 		{
// 			selector: 'edge',
// 			style: {
// 			 	'width': 3
// 			}
// 		}
// 	],
// 	layout: {
// 		name: "circle"
// 	},
// 	userZoomingEnabled: false
// });

console.log(cy);
console.log("hello?\n");

// The styling is based on "data(color)"
// So to change, the style, I just need to change the data.

cy.edges().on("mouseover", function(evt){
	evt.target.data("color", "green");
});

cy.edges().on("mouseout", function(evt){
	evt.target.data("color", "#ccc");
});
