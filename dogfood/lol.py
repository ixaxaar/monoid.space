

alg_structs = {
  'Semigroupoid':     [ 0,1,0,0,0 ],
  'SmallCategory':    [ 0,1,1,0,0 ],
  'Groupoid':         [ 0,1,1,1,0 ],

  'Magma':            [ 1,0,0,0,0 ],
  'Semigroup':        [ 1,1,0,0,0 ],
  'Quasigroup':       [ 1,0,0,1,0 ],
  'Loop':             [ 1,0,1,1,0 ],
  'InverseSemigroup': [ 1,1,0,1,0 ],
  'Monoid':           [ 1,1,1,0,0 ],
  'Group':            [ 1,1,1,1,0 ],
  'AbelianGroup':     [ 1,1,1,1,1 ]
}

laws = ['Totality', 'Associativity', 'Identity', 'Invertibility', 'Commutativity']
root = 'start'


for i, law in enumerate(laws):

def recurse_over_laws(ilaw, tree):

  [ tree + [ k, v[ilaw] ] for k,v in alg_structs.items() ]



recurse_over_laws(law+1)

