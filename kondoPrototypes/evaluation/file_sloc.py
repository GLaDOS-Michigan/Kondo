import sys

def count_sloc_between(file_path, start_line, end_line):
    with open(file_path, 'r') as file:
        lines = file.readlines()

    sloc_count = 0
    in_comment_block = False

    for i, line in enumerate(lines, start=1):
        # Remove leading and trailing whitespaces
        stripped_line = line.strip()

        # Check if the line is part of a multi-line comment
        if '/*' in stripped_line:
            in_comment_block = True

        if not in_comment_block and start_line <= i <= end_line:
            # Check if the line is not a comment or blank
            if stripped_line and not stripped_line.startswith('//'): 
                sloc_count += 1

        if '*/' in stripped_line:
            in_comment_block = False

    return sloc_count

def main():
    if len(sys.argv) != 4:
        print("Usage: python count_sloc.py <file_path> <start_line> <end_line>")
        sys.exit(1)

    file_path = sys.argv[1]
    start_line = int(sys.argv[2])
    end_line = int(sys.argv[3])

    sloc = count_sloc_between(file_path, start_line, end_line)
    print(f'The number of Source Lines of Code (SLOC) between lines {start_line} and {end_line} in {file_path} is: {sloc}')

if __name__ == "__main__":
    main()
