def init():
    global controller_type
    global errorCode
    global character_code_too_many_answers
    global character_code_timeout
    global character_code_inconsistency
    global character_code_complete_run
    global csv_results_file
    global txt_results_file
    global sparc_file

    character_code_too_many_answers = 'A'
    character_code_timeout = 'T'
    character_code_inconsistency = 'I'
    character_code_complete_run = 'C'
    sparc_file = "$HOME/work/solverfiles/sparc_2.jar"
