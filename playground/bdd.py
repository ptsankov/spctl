n = ['out', 'lob', 'cor', 'mr', 'bur']
for x in n:
  for y in n:
    if x == y:
      continue
    if (x, y) not in [('out', 'cor'), ('out', 'lob'), ('cor', 'lob'), ('cor', 'out'), ('cor', 'bur'), ('cor', 'mr'), ('bur', 'cor'), ('mr', 'cor'), ('lob', 'cor'), ('lob', 'out')]:
      continue
    print 'authz_'+ x + '_'+ y + '_ll :='
    print '    case'
    print '      '+ x + '_'+ y + '_ll = vis:'
    print '        visitor;'
    print '      '+ x + '_'+ y + '_ll = not_vis:'
    print '        !visitor;'
    print '      '+ x + '_'+ y + '_ll = empl:'
    print '        employee;'
    print '      '+ x + '_'+ y + '_ll = not_empl:'
    print '        !employee;'
    print '      '+ x + '_'+ y + '_ll = true:'
    print '        TRUE;'
    print '    esac;'
    print 'authz_'+ x + '_'+ y + '_lr :='
    print '    case'
    print '      '+ x + '_'+ y + '_lr = vis: '
    print '        visitor;'
    print '      '+ x + '_'+ y + '_lr = not_vis:'
    print '        !visitor;'
    print '      '+ x + '_'+ y + '_lr = empl:'
    print '        employee;'
    print '      '+ x + '_'+ y + '_lr = not_empl:'
    print '        !employee;'
    print '      '+ x + '_'+ y + '_lr = true:'
    print '        TRUE;'
    print '    esac;'
    print 'authz_'+ x + '_'+ y + '_rl :='
    print '    case'
    print '      '+ x + '_'+ y + '_rl = vis:'
    print '        visitor;'
    print '      '+ x + '_'+ y + '_rl = not_vis:'
    print '        !visitor;'
    print '      '+ x + '_'+ y + '_rl = empl:'
    print '        employee;'
    print '      '+ x + '_'+ y + '_rl = not_empl:'
    print '        !employee;'
    print '      '+ x + '_'+ y + '_rl = true:'
    print '        TRUE;'
    print '    esac;'
    print 'authz_'+ x + '_'+ y + '_rr :='
    print '    case'
    print '      '+ x + '_'+ y + '_rr = vis: '
    print '        visitor;'
    print '      '+ x + '_'+ y + '_rr = not_vis:'
    print '        !visitor;'
    print '      '+ x + '_'+ y + '_rr = empl:'
    print '        employee;'
    print '      '+ x + '_'+ y + '_rr = not_empl:'
    print '        !employee;'
    print '      '+ x + '_'+ y + '_rr = true:'
    print '        TRUE;'
    print '    esac;'

#    print x + '_' + y + '_ll: {vis, not_vis, empl, not_empl, true};'
#    print x + '_' + y + '_lr: {vis, not_vis, empl, not_empl, true};'
#    print x + '_' + y + '_rl: {vis, not_vis, empl, not_empl, true};'
#    print x + '_' + y + '_rr: {vis, not_vis, empl, not_empl, true};'
#    print 'next(' + x + '_' + y + '_ll' + ') := ' + x + '_' + y + '_ll' + ';';
#    print 'next(' + x + '_' + y + '_lr' + ') := ' + x + '_' + y + '_lr' + ';';
#    print 'next(' + x + '_' + y + '_rl' + ') := ' + x + '_' + y + '_rl' + ';';
#    print 'next(' + x + '_' + y + '_rr' + ') := ' + x + '_' + y + '_rr' + ';';

#for x in n:
#  for y in n:
#    if x == y:
#      continue
#    print 'authz_' + x + '_' + y + ' := (' + 'authz_' + x + '_' + y + '_ll' + ' | ' + 'authz_' + x + '_' + y + '_lr'+ ') & (' +  'authz_' + x + '_' + y + '_rl'+ ' | ' + 'authz_' + x + '_' + y + '_rr'+ ');'
