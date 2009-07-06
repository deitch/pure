// examples data
var ex01 = {
	template:'div.who',
	data:{ who:'Hello Wrrrld' }
};

var ex02 = {
	template:'div.hello',
	data:{ who:'Hello Wrrrld' },
	directive:{ 'span.who':'who' }
};

var ex03 = {
	template:'div.friends',
	directive:{
		'.who':'who2.name',
		'.who[title]':'See the tweets of #{who2.twitter}',
		'.who[href]+':'who2.twitter'
	},
	data:{
		friend:[
			{
				name:'Hughes', 
				twitter:'hugheswaroquier'
			},{
				name:'Yves', 
				twitter:'yveshiernaux'
			}
		], 
		who:'dono',
		who2:{
			name:'Mic', 
			twitter:'tchvil'
		}
	}
};

var ex04 = {
	template:'table.playerList',
	directive:{
		'tbody tr':{
			'player<-players':{
				'[class]':function(arg){
					//arg => {data:data, items:items, pos:pos, item:items[pos]};
					var oddEven = (arg.pos % 2 == 0) ? 'even' : 'odd';
					var firstLast = (arg.pos == 0) ? 'first' : (arg.pos == arg.player.items.length - 1) ? 'last' : '';
					return oddEven + ' ' + firstLast;
				},
				'td':'player',
				'td[style]': '"cursor:pointer"',
				'td[onclick]':'"clickLine(this);"'
			}
		}
	},
	data:{
		players:[
			"Adrian Meador","Bryan O'Connor","Michèle Noïjû","تصبح عالميا مع يونيكود",
			"Γέφυρα γρύλων","Chloé Ellemême","глобальных масштабах","יוצא לשוק העולמי",
			"La \"volante\"","Todd Swift","Valerie Paige","Walter Hagelstein","Wendy Leatherbury"
		]
	}
};
function clickLine(elm){
	alert(elm.innerHTML);
}

var ex05 = {
	template:'table.partialTable',
	data:{
		cols:['name', 'food', 'legs'],
		animals:[
			{name:'bird', food:'seed', legs:2},
			{name:'cat', food:'mouse, bird', legs:4},
			{name:'dog', food:'bone', legs:4},
			{name:'mouse', food:'cheese', legs:4}
		]
	},
	directive1:{
		'th':{
			'col<-cols':{
				'.':'col'
			}
		},
		'td':{
			'col<-cols':{
				'[class]':'col'
			}
		}
	},
	directive2:{
		'tbody tr':{
			'animal<-animals':{
				'td.name':'animal.name',
				'td.food':'animal.food',
				'td.legs':'animal.legs'
			}
		}
	}
};

var ex06 = {
	//template:'table.scoreBoard',
	template:'div.scoreBoard',
	data:{
		teams: [{
			name: 'Cats',
			players: [	
				{first: 'Alicé', last: 'Kea\'sler', score: [16, 15, 99, 100]}, 
				{first: '', name: '', score: 0},
				{first: 'Vicky', last: 'Benoit', score: [3, 5]}, 
				{first: 'Wayne', last: 'Dartt', score: [9, 10]}
			]
		},{
			name: 'Dogs',
			players: [
				{first: 'Ray', last: 'Braun', score: 14}, 
				{first: 'Aaron', last: 'Ben', score: 24}, 
				{first: 'Steven', last: 'Smith', score: 1}, 
				{first: 'Kim', last: 'Caffey', score: 19}
			]
		},{
			name: 'Mice',
			players: [
				{first: 'Natalie', last: 'Kinney', score: 16}, 
				{first: 'Caren', last: 'Cohen', score: 3}
			]
		}]
	},
	directive:{
		'tr.scoreBoard': {
			'team <- teams': {
				'td.teamName' : 'team.name',
				'tr.teamList': {
					'player <- team.players': {
						'td.player': '#{player.first} (#{player.last})',
						'td.score': '#{player.score}',
						'td.position': 
							function(arg){
								return arg.pos + 1;
						},
						'[class]+':
							function(arg){
								return (arg.player.pos % 2 == 1) ? ' odd' : ' even';
						}
					}
				}
			}
		}
	}
};

var ex07 = {
	template:'ul.treeItem',
	data:{
		children: [{
			name: 'Europe',
			children: [{
				name: 'Belgium',
				children: [{
					name: 'Brussels'},{
					name: 'Namur'},{
					name: 'Antwerpen'}]},{
				name: 'Germany'},{
				name: 'UK'}]},{
			name: 'America',
			children: [{
				name: 'US',
				children: [{
					name: 'Alabama'},{
					name: 'Georgia'}]},{
				name: 'Canada'},{
				name: 'Argentina'}]},{
			name: 'Asia'},{
			name: 'Africa'},{
			name: 'Antarctica'}
		]
	},
	directive:{
		'li': {
			'child <- children': {
				'a': 'child.name',
				'a[onclick]':'alert(\'#{child.name}\');',
				'div.children': function(ctxt){
					return ctxt.child.item.children ? ex07.rfn(ctxt.child.item):'';
				}
			}
		}
	}
};

var ex08 = function(){
	var	
		// Get the html source (cross lib using $p)
		// adapt it to your library if you want. i.e: $( '#clock' ) for jQuery
		html = $p( '#clock' ),

		// json service returning the current time for a timezone
		tz = 'Europe/Brussels',
		url = 'http://json-time.appspot.com/time.json?tz='+tz+'&callback=showTime&cache=',

		//directive to render the template
		directive = {
			'span.hour': overlay('hour'),
			'span.minute': overlay('minute'),
			'span.second': overlay('second'),
			'span.tz': 'tz'
		},

		// compile the template once
		template = html.compile( directive );

	// utility fn to add leading 0 to numbers
	function overlay(what){
		return function(a){
			var val = a.context[what];
			return val === 0 ? '00' : val < 10 ? '0' + val : val;
		};
	}

	// JSONP load - script injection with callback function (cross lib GET example)
	var noCache = 0;
	function loadTime(){
		var	old = document.getElementById('dataLoad'),
			s = document.createElement("script");
		s.src = url + noCache++;
		!old ? document.body.appendChild(s) : document.body.replaceChild(s, old);
		s.id = 'dataLoad';
	}

	// Render the template
	window.showTime = function(data){
		// rendering but reusing the compiled function template
		html = html.render( data, template );
		// redo it every sec
		window._to = setTimeout( loadTime, 1000 );
	};

	// Call the time service
	loadTime();
};