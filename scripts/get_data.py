import sys
import getopt
import csv
   
colors = ["blue","redpurple","midgreen","clearorange","clearyellow","darkestblue", "browngreen","redpurple","black","darkred"]

colors = ["plotBlue","plotRed","plotGreen","plotPurple","oiBlue","oiOrange","oiGreen","oiVermillion","black","darkred"]
marks = ["x", "+","star","Mercedes star","|"]

def tikz_file_begin ():
  st = """\\documentclass[tikz, border=0pt]{standalone}
  \\usepackage{pgfplots}
  \\usepgfplotslibrary{patchplots}
  \\pgfplotsset{compat=1.16}
  \\usepackage{xspace}

  \\definecolor{oiBlue}{RGB}{0,114,178}
\\definecolor{oiOrange}{RGB}{230,159,0}
\\definecolor{oiGreen}{RGB}{0,158,115}
\\definecolor{oiVermillion}{RGB}{213,94,0}

\\definecolor{plotBlue}{RGB}{0,90,140}
\\definecolor{plotRed}{RGB}{180,60,0}
\\definecolor{plotGreen}{RGB}{0,130,95}
\\definecolor{plotPurple}{RGB}{160,90,130}}

  \\definecolor{redorange}{rgb}{0.878431, 0.235294, 0.192157}
  \\definecolor{lightblue}{rgb}{0.552941, 0.72549, 0.792157}
  \\definecolor{clearyellow}{rgb}{0.964706, 0.745098, 0}
  \\definecolor{clearorange}{rgb}{0.917647, 0.462745, 0}
  \\definecolor{mildgray}{rgb}{0.54902, 0.509804, 0.47451}
  \\definecolor{softblue}{rgb}{0.643137, 0.858824, 0.909804}
  \\definecolor{bluegray}{rgb}{0.141176, 0.313725, 0.603922}
  \\definecolor{lightgreen}{rgb}{0.709804, 0.741176, 0}
  \\definecolor{redpurple}{rgb}{0.835294, 0, 0.196078}
  \\definecolor{midblue}{rgb}{0, 0.592157, 0.662745}
  \\definecolor{clearpurple}{rgb}{0.67451, 0.0784314, 0.352941}
  \\definecolor{browngreen}{rgb}{0.333333, 0.313725, 0.145098}
  \\definecolor{darkestpurple}{rgb}{0.396078, 0.113725, 0.196078}
  \\definecolor{greypurple}{rgb}{0.294118, 0.219608, 0.298039}
  \\definecolor{darktruqoise}{rgb}{0, 0.239216, 0.298039}
  \\definecolor{darkbrown}{rgb}{0.305882, 0.211765, 0.160784}
  \\definecolor{midgreen}{rgb}{0.560784, 0.6, 0.243137}
  \\definecolor{darkred}{rgb}{0.576471, 0.152941, 0.172549}
  \\definecolor{darkpurple}{rgb}{0.313725, 0.027451, 0.470588}
  \\definecolor{darkestblue}{rgb}{0, 0.156863, 0.333333}
  \\definecolor{lightpurple}{rgb}{0.776471, 0.690196, 0.737255}
  \\definecolor{softgreen}{rgb}{0.733333, 0.772549, 0.572549}
  \\definecolor{offwhite}{rgb}{0.839216, 0.823529, 0.768627}


  \\newcommand{\\cadical}{\\textsf{CaDiCaL}}
  \\newcommand{\\modksort}{Extract \\& \\textsf{SortMTot}}
  \\newcommand{\\modksortFifty}{Extract \\& \\textsf{SortMTot}-\\textsf{50}}
  \\newcommand{\\card}{\\textsf{Native}}
  \\newcommand{\\original}{\\textsf{Original}}
  \\newcommand{\\cvctrimtratfive}{\\textsc{cvc5-theory-trim5}\\xspace}

  \\DeclareMathAlphabet\\EuRoman{U}{eur}{m}{n}
  \\SetMathAlphabet\\EuRoman{bold}{U}{eur}{b}{n}
  \\newcommand{\\euler}{\\EuRoman}
  \\begin{document}"""
  return st

def tikz_file_end ():
  return "\n\\end{document}"

def tikz_add_ender():
  return  "\\end{axis}\n\\end{tikzpicture}\n"

def tikz_cactus_header(title,xlabel,ylabel, xmin=0,xmax=6000,ymin=0,ymax=1000):
  s = '''
  \\begin{tikzpicture}[every node/.style={font=\\large}]
  '''
  s += " \\begin{axis} [xlabel="+xlabel+",ylabel="+ylabel+",mark size=3pt,opacity=1,height=8cm,width=8cm,xmin="+str(xmin)+",xmax="+str(xmax)+",ymin="+str(ymin)+",ymax="+str(ymax)+",title={"+title+"},grid=both, grid style={black!10},  legend style={at={(1,0.4)}}, legend cell align={left},]\n"
  return s

def tikz_scatter_header(title,xlabel,ylabel,xmin,xmax,ymin, ymax):
  xmax = max(xmax,ymax)
  ymax = max(xmax,ymax)
  return "\\begin{tikzpicture}[scale = 1]\n\\begin{axis}[mark options={scale=1.0},grid=both, grid style={black!10},  legend style={at={(0.21,0.1)}}, legend cell align={left},\nx post scale=1,xlabel="+xlabel+", ylabel="+ylabel+",mark size=3pt, xmode=log,    ymode=log,height=12cm,width=12cm,xmin="+str(xmin)+",xmax="+str(xmax)+",ymin="+str(ymin)+",ymax="+str(ymax)+",title={"+title+"}]\n"
 
  def tikz_ender():
    return  "\\end{axis}\n\\end{tikzpicture}\n\\end{figure}"

def tikz_cactus_end_stuff(legend, xmax=6000, ymax=1000):

  return "\\addplot[color=black,dashed] coordinates {(0, "+str(ymax)+") ("+str(xmax)+", "+str(ymax)+") };\n"+"\\addplot[color=black,dashed] coordinates {("+str(xmax)+", 0) ("+str(xmax)+", "+str(ymax)+") };\n"+legend+"\n"

def tikz_scatter_end_stuff(legend, timeout=None):
  if timeout is not None:
    st = "\\addplot[color=black, dashed] coordinates {(0.009, " + str(timeout) + ") (100000, " + str(timeout) + ")};\n"
    st += "\\addplot[color=black, dashed] coordinates {(" +str(timeout) + ", 0.009) (" + str(timeout) + ", 100000)};\n"
    st += "\\addplot[color=black] coordinates {(0.009, 0.009) (100000, 100000)};\n"
    return st+(legend)+"\n"
  return "\\addplot[color=black] coordinates {(0.009, 0.009) (100000, 100000)};\n"+legend+"\n"

def tikz_scatter_ender(legend):
  return  "\\addplot[color=black] coordinates {(0.009, 0.009) (100000, 100000)};\n\\"+legend+"\n\\end{axis}\n\\end{tikzpicture}\n\\end{figure}"
  # return  "\\addplot[color=black] coordinates {(0.009, 0.009) (1800, 1800)};\n\\addplot[color=black, dashed] coordinates {(0.009, 1800) (1800, 1800)};\n\\addplot[color=black, dashed] coordinates {(1800, 0.009) (1800, 1800)};\n\\"+legend+"\n\\end{axis}\n\\end{tikzpicture}\n\\end{figure}"







families = [
"edit_distance",
"Kakuro-easy",
"SC21_Timetable",
"Timetable_C_",
"TimetableCNFEncoding",
"baseballcover",
"LABS_n",
"pb_",
"randomG-",
"openstacks-sequencedstrips",
"b1904P",
"ex",
"sted",
"abw-",
"sgen1-sat",
"barman-pfile",
"hole",
"urqh",
"blocks.cnf.mis",
"ais8.cnf.mis",
"SATISFIABLE",
# "9-",
# "8-",
# "6-",
# "5-",
"3blocks",
"bitcomp",
"Num",
"Timetable",
"aim-200",
"frag",
"misc",
"msat-opt",
"ktf"
]

family_names_dic = {
"edit_distance":"cluster dist.",
"Kakuro-easy":"hypertree-decomp",
"SC21_Timetable":"timetable",
"Timetable_C_":"timetable",
"TimetableCNFEncoding":"timetable",
"baseballcover":"bball cover",
"LABS_n":"auto-correlation",
"pb_":"pb",
"randomG-":"random",
"openstacks-sequencedstrips":"openstacks",
"b1904P":"b1904",
"ex":"tree-decomp",
"sted":"sted",
"abw-":"abw",
"sgen1-sat":"sgen1",
"barman-pfile":"barman",
"hole":"hole",
"urqh":"urqh",
"blocks.cnf.mis":"blocks",
"ais8.cnf.mis":"ais8",
"SATISFIABLE":"sat",
# "9-":"num",
# "8-":"num",
# "6-":"num",
# "5-":"num",
"3blocks":"blocks",
"bitcomp":"bitcomp",
"Num":"num",
"Timetable":"timetable",
"frag":"msat-opt",
"misc":"misc",
"msat-opt":"sat-opt",
"ktf":"RBT"
}

family_unknown = [
"LABS_n",
]

family_seq =[
"Kakuro-easy",
"SC21_Timetable",
"Timetable_C_",
"TimetableCNFEncoding",
"baseballcover",

"pb_",
"randomG-",
"openstacks-sequencedstrips",
"b1904P",
"abw-",
"sgen1-sat",
"barman-pfile",
"hole",
"urqh",
"blocks.cnf.mis",
"ais8.cnf.mis",
"SATISFIABLE",
"9-",
"8-",
"6-",
"5-",
"3blocks",
"bitcomp",
"Timetable",
"misc",
"msat-opt"
]

family_to = [
  "edit_distance",
"sted","Num", "ktf", "ex"
]




'''

Print a scatter with 

scatters: [(x, y)]
title: string
xaxis: string
yaxis: string
legend: [string]


'''
def print_scatter (scatters, title,xaxis,yaxis,legend):
  xmax = 0
  ymax = 0

  i = 0

  sts = []
  for (f,s) in scatters:
    if f > xmax: xmax = f
    if s > ymax: ymax = s 

    # If you wanted to get more complicated, you could make each point in scatters a tuple with 
    # four elements (f,s,c,m), where c and m are the color and mark for a given 
    # benchmark. For example, you could give SAT instances the color blue (0) and 
    # UNSAT (1) instances the color red. You colud also change the size of the mark 
    # or the type of mark depending on the size of the formula. 

    line = "\\addplot[color="+colors[i]+",mark="+marks[i]+",opacity=0.5] coordinates { ("+str(f) + "," + str(s) + ") };"
    sts.append(line)

  print(tikz_scatter_header (title,xaxis, yaxis,xmax+100,ymax+100))
  for st in sts: print(st)

  print(tikz_scatter_ender("legend{"+", ".join(legend)+"}"))  


def tikz_scatter_addplotF (mark,color,name, markSize):
  s = ""
  s += "\\addplot [opacity=0.9,"+color+",mark size="+str(markSize)+"pt, "
  s += "scatter, point meta=explicit symbolic,\nscatter/classes={"
  l = ""
  cnt = 0
  l += f"{name}={{mark={mark},{color}}},"
  s += l[:-1] + "}\n"
  s += "] coordinates {\n"
  return s

def print_scatter_solve (scatters,config1, config2, title,xaxis,yaxis,legend, xmin=1,xmax=500,ymin=1,ymax=300, first=False, last=False, only_solve=False):
  timeout = 5000
  i = 0

  big_bs = []
  if first: 
    print(tikz_file_begin())
  print(tikz_scatter_header (title,xaxis, yaxis, xmin,xmax,ymin+500,ymax+500))

  for result in ["SAT", "UNSAT"]:
    lab = "l"+str(i)
    markSize = 3
    print(tikz_scatter_addplotF (marks[i],colors[i],lab,markSize))
    for scat in scatters:
      if scat["result"] != result:
        continue

      f = scat[config1]
      s = scat[config2]

      sdiff = scat["extract_time"] 

      if f < xmin: f = xmin
      if s < ymin: s = ymin

      if f <= 20 and s >= 50: 
        big_bs.append(scat['b'])

      lower = s-sdiff
      if lower < ymin: lower = ymin

      if f >= timeout and s >= timeout:
        continue
      if only_solve:
        print(f"({f},{lower}) [{lab}]\n\n") 
      else:
        print(f"({f},{s}) [{lab}]\n ({f},{lower}) [{lab}]\n\n") # [{lab}]")
    print("};")
    i += 1
  
  # for st in sts: print(st)
  print(tikz_scatter_end_stuff("\\legend{"+", ".join(legend)+"}", timeout))
  print(tikz_add_ender())
  
  if last: 
    print(tikz_file_end())

  for b in big_bs:
    print(f"Benchmark {b}")

def print_scatter_size (scatters,title,xaxis,yaxis,legend, xmin=1,xmax=500,ymin=1,ymax=300, first=False, last=False):
  i = 0
  if first: 
    print(tikz_file_begin())
  
  xmax = 0 
  ymax = 0
  for s,b in scatters:
    if s > xmax: xmax = s
    if b > ymax: ymax = b

  scat_axis = max(xmax, ymax) + 100
  print(tikz_scatter_header (title,xaxis, yaxis, xmin,scat_axis,ymin,scat_axis))
  lab = "l"+str(i)
  markSize = 3
  print(tikz_scatter_addplotF (marks[i],colors[i],lab,markSize))
  for s,b in scatters:
    if s > xmax: xmax = s
    if b > ymax: ymax = b
    print(f"({s},{b}) [{lab}]\n") 
  print("};")

  # for st in sts: print(st)
  print(tikz_scatter_end_stuff(""))
  print(tikz_add_ender())
  
  if last: 
    print(tikz_file_end())


def print_cactus_scale (encodings,cactus,title,xaxis,yaxis,legend, xvert_max, yvert_max=500,xmin=0,xmax=500,ymin=0,ymax=300, first=False, last=False):
  i = 0
  sts = []
  big_ps = []
  for encoding in encodings:
    mark = 0
    for ratio in [0.5,0.25]:
      if ratio == 0.25:
        line = "\\addplot[dashed,thick,color="+colors[i]+",mark="+marks[mark]+",opacity=0.75] coordinates { "
      else: 
        line = "\\addplot[thick,color="+colors[i]+",mark="+marks[mark]+",opacity=0.75] coordinates { "
      prev_bound = None
      prev_runtime = None
      for (bound,runtime) in cactus[encoding][ratio]:
        if runtime >= ymax: 

          # save big plot point for later printing as a star
          sbp = "\\addplot[color="+colors[i]+",mark=*,opacity=1, mark size=3pt] coordinates { "
          if prev_bound is not None: 
            sbp += " ("+str(prev_bound) + "," + str(prev_runtime) + ") "
          sbp += "};\n"
          big_ps.append(sbp)
          break

        line += " ("+str(bound) + "," + str(runtime) + ") "
        prev_bound = bound
        prev_runtime = runtime
      line += "};"
      sts.append(line)
      mark += 1
    i += 1
    
  if first: 
    print(tikz_file_begin())
  print(tikz_cactus_header (title,xaxis, yaxis, xmin,xvert_max,ymin,yvert_max))
  # Print odd then even lines
  for j in range(len(sts)//2):
    print(sts[2*j])
  for j in range(len(sts)//2):
    print(sts[2*j+1])

  for bp in big_ps:
    print(bp)
  
  # for st in sts: print(st)
  print(tikz_cactus_end_stuff("\\legend{"+", ".join(legend)+"}", xmax, ymax))
  print(tikz_add_ender())
  
  if last: 
    print(tikz_file_end())

# Name,total1,total2
def get_csv_data_with_filenames (file) :
  candidates = []
  solve_stats = {}
  with open(file, mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      temp_b = line["Filename"] # benchmark name
      candidates.append(temp_b)
      solve_stats[temp_b] = line
  return solve_stats, candidates

def get_extraction_sizes (file) :
  sizes = {}
  with open(file, mode='r') as file:
    for line in file:
      data = {'min_size':None , 'max_size':None, 'mean_size':None, 'count':None, 'bound_ratio':None, 'line':None}
      #name is up to first comma
      name = line.split(",")[0]
      ex_list = line[line.find(",")+1:].strip() # everything after first comma
      # ex_list is a list of extraction sizes (size,bound):count
      # For example (43,42):27 (43,4):36 (43,38):18 (43,3):102 (43,39):36 (43,5):18 (43,40):102 (43,2):148 (43,41):148 

      # First get it in a dictionary indexed by size and bound
      ex_dict = {}
      # Need to split by spaces; then split by colon to get size, bound, and count
      bound_ratio_sum = 0 
      for ex in ex_list.split(" "):
        if ex == "":
          continue
        size_bound, count = ex.split(":")
        # print(size_bound)
        size_bound = size_bound.strip()[1:-1] # remove parentheses
        # print(size_bound)
        size, bound = size_bound.split(",")
        size = int(size)
        bound = int(bound)
        count = int(count)
        ex_dict[(size,bound)] = count
        if bound > size/2: 
          bound = size - bound

        bound_ratio_sum += bound * float(count) / size if size > 0 else 0

      data['min_size'] = min(ex_dict.keys(), key=lambda x: x[0])[0] if ex_dict else None
      data['max_size'] = max(ex_dict.keys(), key=lambda x: x[0])[0] if ex_dict else None
      data['count'] = sum(ex_dict.values()) if ex_dict else 0
      data['bound_ratio'] = bound_ratio_sum / data['count'] if data['count'] > 0 else 0
      data['line'] = ex_dict
      sizes[name] = data
  return sizes

def get_largest_extraction_size (extraction_size_data):
  max_size = 0
  corresponding_bound = 0
  for (size, bound), count in extraction_size_data['line'].items():
    if size > max_size:
      max_size = size
      corresponding_bound = bound
  return max_size, corresponding_bound

def get_csv_data_scale (file) :
  solve_stats = {}
  with open(file, mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      key = (line["encoding"], line["size"], line["bound"], line["verification"])
      solve_stats[key] = line
  return solve_stats

# f, s are configurations to compare for each benchmark
def get_scatter_vals (stats, f,s,candidates):
  scatters = []
  for b in candidates:
    scatters.append((float(stats[b][f]),float(stats[b][s])))
  return scatters

def get_solve_time (stats_line, b, is_checked, config):
  timeout = 5000
  solve_real_time = stats_line["solve_real_time"]
  if solve_real_time is not None and float(solve_real_time) > timeout:
    return timeout
  if is_checked:
    if stats_line["SAT_verified"] != "1":
      print(f"Warning: benchmark {b} was not verified as SAT, but is marked as SAT in the data. Setting solve time to timeout. Configuration: {config}")
      exit ()
      return timeout
  if solve_real_time is not None:
    if float(solve_real_time) < 0:
      return timeout
    else:
      return float(solve_real_time)
  else:
    print(f"Warning: solve_real_time is None for benchmark {b}. Setting solve time to timeout. Configuration: {config}")
    return timeout


def combine_solve_configs (config1, config2, config_new, solve_stats, extraction_sizes, benchmarks, combine_type):
  new_stats = {}
  nCombined = 0
  for b in benchmarks: 
    if combine_type == "kmod-50":
      if extraction_sizes[b]['min_size'] < 50:
        new_stats[b] = solve_stats[config1][b]
        nCombined += 1
      else:
        new_stats[b] = solve_stats[config2][b]

  solve_stats[config_new] = new_stats

  print(f"Combined {nCombined} benchmarks from {config1} and {len(benchmarks)-nCombined} benchmarks from {config2} to create new configuration {config_new}.")

TexNames = {'card':"Extract\\&\\native" , "cadical":"\\original", "knf2cnf":"\\knfDirect", "modk-sort":"\\modksort", "kmod-50":"Extract\\&\\modksortFifty"}

def compare_solve_data(solve_stats, benchmarks, configs, extraction_data=None, with_encoding=True, with_extraction=False):
  timeout = 5000
  data_points = []
  data = {}
  scatters = []
  for c in configs: data[c] = {'rt':0, 'unsolved':0, 'BestSAT':0, "BestUNSAT":0, "solvedSAT":0, "solvedUNSAT":0, "uniqueSolvedSAT":0, "uniqueSolvedUNSAT":0}
  for b in benchmarks:
    l = {}
    # no_contest = False
    best_rt = float('inf')
    best_config = None
    result = None
    extract_time = None
    scat = {}
    nSolved = 0
    for c in configs:
      # if b not in solve_stats[c]:
      #   no_contest = True
      #   continue
      stats_line = solve_stats[c][b]
      rt = get_solve_time(stats_line, b, False, c)

      if with_extraction and c not in ["cadical"]:
        # print(f"Adding extraction time for benchmark {b} and configuration {c}.")
        extraction_rt = float(extraction_data[b]["extraction_real_time"]) + float(extraction_data[b]["ple_real_time"])
        extract_time = extraction_rt
        rt += extraction_rt
        if rt > timeout:
          rt = timeout
      if with_encoding and c in ["knf2cnf", "modk-sort"]:
        encoding_rt = float(stats_line["encoding_real_time"])
        rt += encoding_rt
        if rt > timeout:
          rt = timeout
      rt = round(rt, 2)
      scat[c] = rt
      l[c] = rt
      if rt >= timeout:
        data[c]['unsolved'] += 1
      else:
        nSolved += 1
        if stats_line["exit_code"] == "10":
          data[c]["solvedSAT"] += 1
          result = "SAT"
        elif stats_line["exit_code"] == "20":
          data[c]["solvedUNSAT"] += 1
          result = "UNSAT"
        data[c]['rt'] += rt
        if rt < best_rt:
          best_rt = rt
          best_config = c
    # if no_contest:
    #   continue
    if best_config is not None:
      if result == "SAT":
        data[best_config]['BestSAT'] += 1
        if nSolved == 1:
          data[best_config]['uniqueSolvedSAT'] += 1
          print(f"Benchmark {b} result {result} was uniquely solved by {best_config} with rt {best_rt}..")
      elif result == "UNSAT":
        data[best_config]['BestUNSAT'] += 1
        if nSolved == 1:
            data[best_config]['uniqueSolvedUNSAT'] += 1
            print(f"Benchmark {b} result {result} was uniquely solved by {best_config} with rt {best_rt}.")
      else: 
        print(f"Warning: benchmark {b} was solved but has unknown result. Not counting it as a win for any configuration. Best configuration: {best_config}")
        exit (1)
    data_points.append((b,l))
    scat["result"] = result
    scat["extract_time"] = extract_time
    scat['b'] = b
    scatters.append(scat)
  
  # sort based on difference between two configurations
  print_full = False 
  if print_full:
    config1 = "cadical"
    config1 = "knf2cnf"
    config2 = "modk-sort"
    # config2 = "card"
    data_points.sort(key=lambda x: x[1][config1] - x[1][config2], reverse=True)

    print(f"{'Difference':<10} {config1:<10} {config2:<10} Benchmark")
    for b, l in data_points:
      diff = round(l[config1] - l[config2], 2)
      print(f"{diff:<10} {l[config1]:<10} {l[config2]:<10} {b[33:]}")

  # Print summary data
  lines = []
  print(f"{'Configuration':<15} {'Avg Par2':<15} {'Unsolved':<15} {'Best SAT':<15} {'Best UNSAT':<15} {'Solved SAT':<15} {'Solved UNSAT':<15} {'Unique Solved SAT':<20} {'Unique Solved UNSAT':<20}")
  for c in configs:
    if data[c]['rt'] > 0:
      avg = ((data[c]['unsolved'] * timeout * 2) + data[c]['rt']) / (len(benchmarks))
    else:
      avg = 0
    line = f"{c:<15} {int(avg):<15} {data[c]['unsolved']:<15} {data[c]['BestSAT']:<15} {data[c]['BestUNSAT']:<15} {data[c]['solvedSAT']:<15} {data[c]['solvedUNSAT']:<15} {data[c]['uniqueSolvedSAT']:<20} {data[c]['uniqueSolvedUNSAT']:<20}"
    lines.append(line)
    print(line)
  # Print with tikz formatting, & after ever entry and \\ at the end of the line
  print("\nTikz formatted summary:")
  for line in lines:
    # replace config with name from TexNames
    for config in TexNames.keys():
      line = line.replace(config, TexNames[config])
    print(" & ".join(line.split()) + " \\\\")

  return scatters

def get_scale_time (stats, key):
  timeout = 1000
  
  if key not in stats:
    return timeout
  if stats[key]["success"] != "true":
    return timeout
  if stats[key]["real_time"] is None:
    return timeout
  if stats[key]["real_time"] == "":
    return timeout
  rt = float(stats[key]["real_time"])
  if rt > timeout:
    return timeout
  return rt

def get_cactus_data_scale (stats, verification, encodings): 
  cactus = {}

  bounds = []
  if verification == "bdd":
    bounds = [str(i) for i in range(25, 201, 25)] + [str(i) for i in range(200, 401, 50)]
  elif verification == "sat": 
    bounds =  [str(i) for i in range(50, 801, 50)]
  elif verification == "testing":
    bounds =  [str(i) for i in range(50, 2001, 50)]

  verification_key = 0
  if verification == "bdd":
    verification_key = "2"
  elif verification == "sat":
    verification_key = "1"
  elif verification == "testing":
    verification_key = "0"

  for encoding in encodings:
    tlist = {}
    for ratio in [0.25, 0.5]: 
      nList = []
      for bound in bounds:
        key = (encoding, bound, str(int(float(ratio) * int(bound))), verification_key)
        rt = get_scale_time(stats, key) 
        nList.append((int(bound), rt))
      tlist[ratio] = nList
    cactus[encoding] = tlist

  return cactus

def filter_only_AMO (benchmarks, extraction_sizes):
  filtered = []
  for b in benchmarks:
    is_AMO = True
    for (size, bound), count in extraction_sizes[b]['line'].items():
      if bound != size - 1:
        is_AMO = False
        break
    if not is_AMO : #or "pb_" in b:
      filtered.append(b)
  return filtered

def find_family (benchmark, alk_count):
  if "dist" not in benchmark and "baseball" not in benchmark and "LABS" not in benchmark and alk_count == 1:
    return "msat-opt"
  for f in families:
    if f in benchmark:
      if f in ["4-", "5-", "6-", "8-", "9-"]:
        f = "Num"
      if f in ["Timetable_C_", "TimetableCNFEncoding", "SC21_Timetable"]:
        f = "Timetable"
      if f in ["aim-200"]:
        f = "ais8.cnf.mis"
      if f in ["bitcomp"]:
        f = "Kakuro-easy"
      # if f in ["frag"]:
      #   f = 

      return f

  print(f"Warning: could not find family for benchmark {benchmark}. Returning misc.")
  f = "misc"
  return f
  return None

def get_extraction_table(benchmarksSeq, benchmarksTot, extraction_data, extraction_sizes):
  print(len(benchmarksSeq), len(benchmarksTot))
  lines = []
  for bs in [benchmarksSeq, benchmarksTot]:
    data = {}
    for f in families: data[f] = {'total_rt':0, 'tot_klauses':0,'count':0, 'min_size':float('inf'), 'max_size':0, 'bound_ratio_sum':0, 'cache-hits':0}
    for b in bs: 
      f = find_family(b,extraction_sizes[b]['count'])
      if f == "misc" : print(b)
      if family_names_dic[f] == "msat-opt": print(b)
      data[f]['count'] += 1
      data[f]['total_rt'] += float(extraction_data[b]['extraction_real_time']) + float(extraction_data[b]['ple_real_time'])
      data[f]['cache-hits'] += int(extraction_data[b]['cache_hits_verified']) if 'cache_hits_verified' in extraction_data[b] and extraction_data[b]['cache_hits_verified'] is not None else 0
      data[f]['tot_klauses'] += extraction_sizes[b]['count']
      if extraction_sizes[b]['min_size'] < data[f]['min_size']:
        data[f]['min_size'] = extraction_sizes[b]['min_size']
      if extraction_sizes[b]['max_size'] > data[f]['max_size']:
        data[f]['max_size'] = extraction_sizes[b]['max_size']
      data[f]['bound_ratio_sum'] += extraction_sizes[b]['bound_ratio']

    print(f"Data for {'Sequential' if bs == benchmarksSeq else 'Totalizer'}:")
    print(f"{'Family':<20} {'Encoding':<20}  {'Count':<10} {'Avg RT':<10} {'Avg #Clauses':<15} {'Min Size':<10} {'Max Size':<10} {'Avg Bound Ratio':<20} {'Cache Hits':<15}")
    for f in data.keys():
      if data[f]['count'] > 0:

        if f in family_seq: encoding = "\\seqCnt"
        elif f in family_to: encoding = "\\totalizer"
        else: encoding = "Unknown"

        line = f"{family_names_dic[f]:<20} {encoding:<20}  {data[f]['count']:<10} {int(data[f]['total_rt']/data[f]['count']):<10} {int(data[f]['tot_klauses']/data[f]['count']):<15} {data[f]['min_size']:<10} {data[f]['max_size']:<10} {data[f]['bound_ratio_sum']/data[f]['count']:<20.2f} {int(data[f]['cache-hits']/data[f]['count']):<15}"
        print(line)
        lines.append(line)
    print("\nTikz formatted summary:")
    for line in lines:
      # replace family with name from family_names_dic
      print(" & ".join(line.split()) + " \\\\")

def compare_scran_data(benchmarks, extraction_data, extraction_sizes, scran_data, scran_sizes): 
  info = {'all':0, 'partial':0, 'none':0, 'oRt':0, 'sRt':0}
  for b in benchmarks:
    scran_alk = scran_data[b]['alk_constraints'] if b in scran_data and 'alk_constraints' in scran_data[b] and scran_data[b]['alk_constraints'] is not None else 0
    o_alk = extraction_data[b]['alk_constraints'] if b in extraction_data and 'alk_constraints' in extraction_data[b] and extraction_data[b]['alk_constraints'] is not None else 0
    if int(o_alk) > 0 :
      if int(scran_alk) >= int(o_alk):
        info['all'] += 1
      elif int(scran_alk) > 0:
        info['partial'] += 1
      else:
        print(f"benchmark{b} o_ALK {o_alk} s_ALK {scran_alk}")
        info['none'] += 1

    # if 'extraction_real_time' not in 
    sRt = float(scran_data[b]['extraction_real_time']) + float(scran_data[b]['ple_real_time'])
    oRt = float(extraction_data[b]['extraction_real_time']) + float(extraction_data[b]['ple_real_time'])
    info['oRt'] += oRt
    info['sRt'] += sRt
  print(f"All: {info['all']}, Partial: {info['partial']}, None: {info['none']}, Avg Original RT: {round(info['oRt']/len(benchmarks))}, Avg Scran RT: {round(info['sRt']/len(benchmarks))}")



def process_data (data_type, plots): 

  solve_stats = {}
  candidates = {}
  csv_directory = "data/"

  seq_extraction_sizes = get_extraction_sizes (csv_directory + "grid-extract-sizes.txt")
  seq_extraction_data, t = get_csv_data_with_filenames (csv_directory + "grid-extract.csv")
  
  tot_extraction_sizes =  get_extraction_sizes (csv_directory + "hier-extract-sizes.txt")
  tot_extraction_data, t =  get_csv_data_with_filenames (csv_directory + "hier-extract.csv")

  tot_dist_extraction_sizes =  get_extraction_sizes (csv_directory + "hier-extract-sizes-dist-noveri.txt")
  tot_dist_extraction_data, t = get_csv_data_with_filenames (csv_directory + "hier-extract-dist-noveri.csv")

  # Add edit_distance with only random-testing
  add_edit = False 
  if add_edit: 
    for b in tot_dist_extraction_data.keys():
      tot_extraction_sizes[b] = tot_dist_extraction_sizes[b]
      tot_extraction_data[b] = tot_dist_extraction_data[b]

  tot_candidates = list(tot_extraction_sizes.keys())
  seq_candidates = list(seq_extraction_sizes.keys())
  full_extraction_data = {}
  full_extraction_sizes = {}
  for b in seq_candidates:
    if "magic" in b: # magic squares problem added to benchmark set for testing
      continue
    full_extraction_data[b] = seq_extraction_data[b]
    full_extraction_sizes[b] = seq_extraction_sizes[b]
  for b in tot_candidates:
    if "magic" in b: 
      continue
    if b not in full_extraction_data:
      full_extraction_data[b] = tot_extraction_data[b]
      full_extraction_sizes[b] = tot_extraction_sizes[b]

  full_extraction_candidates = list(full_extraction_data.keys())

  if data_type == "solve":
    
    solve_stats['cadical'], candidates['cadical'] = get_csv_data_with_filenames (csv_directory + "original-cadical-solve.csv")
    solve_stats['knf2cnf'], candidates['knf2cnf'] = get_csv_data_with_filenames (csv_directory + "knf2cnf-solve.csv")
    solve_stats['modk-sort'], candidates['modk-sort'] = get_csv_data_with_filenames (csv_directory + "modksorted-solve.csv")

    solve_stats['knf2cnf-tot'], candidates['knf2cnf-tot'] = get_csv_data_with_filenames (csv_directory + "knf2cnf-hier-solve.csv")
    solve_stats['modk-sort-tot'], candidates['modk-sort-tot'] = get_csv_data_with_filenames (csv_directory + "modksorted-hier-solve.csv")

    # add totalizer data to original data
    for b in candidates['knf2cnf-tot']: 
      if b not in candidates['knf2cnf']:
        candidates['knf2cnf'].append(b)
        solve_stats['knf2cnf'][b] = solve_stats['knf2cnf-tot'][b]
        candidates['modk-sort'].append(b)
        solve_stats['modk-sort'][b] = solve_stats['modk-sort-tot'][b]

    benchmarks = full_extraction_candidates
    # Remove benchmark with magic in name 
    benchmarks = [b for b in benchmarks if "magic" not in b]
    benchmarks = filter_only_AMO(benchmarks, full_extraction_sizes)


    combine_solve_configs("knf2cnf","modk-sort", "kmod-50", solve_stats, full_extraction_sizes, benchmarks, "kmod-50")

    configs = ["cadical", "kmod-50"]
    compare_solve_data(solve_stats, benchmarks, configs, full_extraction_data,True, False)
    print(f"Total benchmarks: {len(benchmarks)}")

    # Combine with extraction data
    scatters = compare_solve_data(solve_stats, benchmarks, configs,full_extraction_data, True, True)
    if plots:

      print_scatter_solve (scatters, "cadical", "kmod-50", "Solving With and Without Extraction Time", "\\cadical", "\\modksortFifty", ["SAT","UNSAT"], xmin=10,xmax=5000,ymin=10,ymax=5000, first=True, last=True)

      # print_scatter_solve (scatters, "cadical", "kmod-50", "Solving Minus Extraction Time", "\\cadical", "\\modksortFifty", ["SAT","UNSAT"], xmin=10,xmax=5000,ymin=10,ymax=5000, first=True, last=True, only_solve=True)


  elif data_type == "extract":
    benchmarksSeq = filter_only_AMO(seq_candidates, seq_extraction_sizes)
    benchmarksTot = filter_only_AMO(tot_candidates, tot_extraction_sizes)

    get_extraction_table(benchmarksSeq, [], seq_extraction_data, seq_extraction_sizes)

    print("\n\n*********Totalizer********* \n")

    get_extraction_table([], benchmarksTot, tot_extraction_data, tot_extraction_sizes)


    print("Total average time")
    tot = 0
    bs = list (seq_extraction_data.keys())
    for b in bs:
      total_rt = 1000
      if seq_extraction_data[b]['extraction_real_time'] is not None:
        total_rt = float(seq_extraction_data[b]['extraction_real_time']) + float(seq_extraction_data[b]['ple_real_time'])
      tot += total_rt
    print(f"SEQCNT: Average total extraction time: {round(tot/len(bs), 2)} seconds on {len(bs)} benchmarks")
    print("Total average time")
    tot = 0
    bs = list (tot_extraction_data.keys())
    for b in bs:
      total_rt = 1000
      if tot_extraction_data[b]['extraction_real_time'] is not None:
        total_rt = float(tot_extraction_data[b]['extraction_real_time']) + float(tot_extraction_data[b]['ple_real_time'])
      tot += total_rt
    print(f"Totalizer; Average total extraction time: {round(tot/len(bs), 2)} seconds on {len(bs)} benchmarks")
    # get duplicated in bs
    dup_cnt = 0 
    for i in range(len(bs)):
      if bs[i] in bs[:i]:
        dup_cnt += 1
    print(f"Totalizer: {dup_cnt} duplicated benchmarks in totalizer extraction data.")
    for b in bs: 
      if b not in list(seq_extraction_data.keys()):
        print(f"Warning: benchmark {b} in totalizer extraction data but not in sequential extraction data.")

  elif data_type == "scale":
    solve_stats['scale'] = get_csv_data_scale (csv_directory + "scaling.csv")
    for verification in ["bdd", "sat", "testing"]:
      encodings=["seqcounter", "cardnetwrk", "totalizer", "kmtotalizer"]
      cactus = get_cactus_data_scale(solve_stats['scale'], verification, encodings)
      # print(solve_stats['scale'])
      # print(cactus)
      ymax = 0
      xext_max = 1100
      xmax = 1000
      legend = ["seq", "card","tot","kmtot"]
      if verification == "bdd":
        ymax = 400
        yext_max = 500
        xmax = 400
        legend = ["seq", "card","tot","kmtot"]
      elif verification == "sat":
        ymax = 1000
        yext_max = 900
        xmax = 800
      elif verification == "testing":
        ymax = 400
        yext_max = 2100
        xmax = 2000 
        xext_max = 550

      yext_max = ymax
      xext_max = xmax
      
      vname = {'bdd':"BDD", 'sat':"SAT", 'testing':"Random Testing"}
      title = f"Verification with {vname[verification]}"
      if verification == "testing":
        tile = f"Random-Testing Prefilter"
      print_cactus_scale(encodings, cactus, title, "Size","Runtime (s)", legend, xext_max,yext_max, xmin=0,xmax=xmax,ymin=0,ymax=ymax, first=(verification == "bdd"), last=(verification == "testing"))
      print("\n\n")
 


  

#######################################################################################
# MAIN FUNCTION
#######################################################################################
  
def run(name, args):

  data_type = None
  plots = False
        
  optlist, args = getopt.getopt(args, "pt:")
  for (opt, val) in optlist:
    if opt == '-t':
      data_type = val
    if opt == '-p':
      plots = True

  process_data(data_type, plots)
        

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
