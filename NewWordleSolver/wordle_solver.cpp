/**
 * @file wordle_solver.c
 * @brief An entropy-based Wordle puzzle solver using a dynamic Rank/Entropy trade-off.
 *
 * This program implements a Wordle solver designed to find the mathematically optimal
 * next guess by balancing information theory (Shannon Entropy) with word frequency
 * and linguistic constraints.
 *
 * --- Core Metrics and Rationale ---
 *
 * **RANK DEFINITION (R):**
 * - Rank (000-100): Indicates word frequency/likelihood. 100 = MOST COMMON; 000 = LEAST COMMON.
 * - Purpose: Used as a tie-breaker when Entropy (H) scores are close, and as the primary
 * metric when the set of possible answers is small.
 *
 * **ENTROPY CALCULATION (H):**
 * - Shannon Entropy (H) is calculated for each guess against the set of possible answers.
 * - **Formula:** H = $\sum_{k=1}^{M} P_k \cdot \log_2(\frac{1}{P_k})$, where $P_k$ is the probability
 * of obtaining a specific color pattern result (Green/Yellow/Black) out of the $M$ possible results.
 * - Purpose: Maximizing H corresponds to the word that, on average, provides the most
 * information and reduces the set of possible answers most efficiently.
 *
 * --- Overall Process and Final Pick Logic ---
 *
 * 1. **Data Initialization:** Loads the local dictionary (with R and linguistic tags) and fetches/filters
 * the list of past Wordle answers from an external URL using cURL.
 * 2. **Constraint Update (Turn-based):** Reads the user's guess and the G/Y/B result pattern,
 * and updates four key constraints: Green Mask, Required Letters (min count), Excluded Letters,
 * and Positional Exclusions. (Refactored to `update_game_constraints`).
 * 3. **Recommendation Cycle:**
 * a. **Metric Calculation:** H, R, Linguistic Types, and Repeat Risk are calculated for all
 * remaining possible answers. (Refactored to `calculate_all_metrics`).
 * b. **Sorting:** Two independent, filtered lists are generated: one prioritized by H, the other by R.
 * c. **Dynamic Pick:** The final word selection uses a dynamic trade-off:
 * - **Large Set (N > 25):** Prioritize H, unless the H difference is below a 0.50 threshold,
 * in which case the higher R word is chosen.
 * - **Small Set (N <= 25):** Prioritize the word with the absolute highest R.
 *
 * --- External Data Specification ---
 *
 * 1. **Local Dictionary File (Hardcoded Path: "C:\\VS2022.Projects\\StuffForWordle\\WordleWordsCSVs\\AllWords.txt")**
 * - **Purpose:** Provides a comprehensive list of 5-letter words with associated frequency and linguistic metadata
 * used for filtering and scoring.
 * - **Format:** Each line contains exactly 10 contiguous characters (no delimiter).
 * `[Word (5 chars)][Rank (3 chars)][Noun Type (1 char)][Verb Type (1 char)]`
 * - **Example Line:** `ABETS070NS` (ABETS, Rank 070, Not Noun, Singular Present).
 * - **Field Domain Values:**
 * - **Rank (R):** Numerical frequency score from **000** (Least Common) to **100** (Most Common).
 * - **Noun Type (Plurality) Codes:**
 * - **'S':** Singular Noun (e.g., APPLE).
 * - **'P':** Plural Noun **(FILTERED: Excluded from solution set)**.
 * - **'N':** Not a Noun or Noun form irrelevant (e.g., ADAPT).
 * - **Verb Type (Preterite) Codes:**
 * - **'P':** Present/Base Form (e.g., CARE, DRIVE).
 * - **'S':** Singular Present Tense (3rd Person) **(FILTERED: Excluded)**.
 * - **'T':** Past Tense/Preterite **(FILTERED: Excluded)**.
 * - **'N':** Not a Verb or Verb form irrelevant (e.g., ABOUT).
 *
 * 2. **Web Scraped Used Words (URL: "https://www.rockpapershotgun.com/wordle-past-answers")**
 * - **Purpose:** Words are excluded from the list of "possible answers" unless explicitly flagged
 * for replay in the `g_wordle_replay_words` array.
 */

#include <Windows.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <errno.h>
#include <stdbool.h>
#include <curl/curl.h>
#include <math.h>
#include <stdarg.h>

#define LOW_POSSIBLE_ANSWER_COUNT 25
#define WORD_SIZE 5
#define MAX_DICTIONARY_WORDS 200000
#define EPSILON 1e-9

 // Macro to check if float 'a' is strictly greater than float 'b', accounting for precision
#define FLOAT_GREATER(a, b) ((a) > (b) + EPSILON)

// Global definition for the threshold difference in Entropy (H) below which Rank (R) is prioritized.
#define ENTROPY_RANK_THRESHOLD 0.50

// Global debug controls
#define DEBUG_ON 1
#define DEBUG_LEVEL 0 // 0 = print all debug, higher number limits debug output to later turns
#define MAX_TOP_PICKS 40

// --- Global Variables and Replay List ---
long numUsedWords = 0;
long numWordsInDictionary = 0;
long maxDictionary = MAX_DICTIONARY_WORDS;
int g_tryIdx = 0; // Tracks the current guess index (1-6)

// Replay words: Past answers explicitly included in the possible answers set for simulation.
//#define NUM_REPLAY_WORDS 7
#ifdef NUM_REAPLAY_WORDS
char g_wordle_replay_words[NUM_REPLAY_WORDS][WORD_SIZE + 1] =
{
    "ABHOR", "LATHE", "GLARE", "HOLLY", "FETID", "PLUMP", "GAUGE"
};
#endif

// --- Data Structures ---

/**
 * @brief Structure to hold dictionary data for a word.
 */
typedef struct _word_entry
{
    char word[WORD_SIZE + 1];
    int rank;
    char nounType;
    char verbType;
} WORD_ENTRY, * PWORD_ENTRY;

/**
 * @brief Node for a dynamically allocated linked list, repurposed for pattern counting in Entropy calculation.
 * 'word' holds the 5-char pattern (e.g., "BGYBB"), 'rank' holds the count.
 */
typedef struct _word_node
{
    char word[WORD_SIZE + 1];
    int rank;
    struct _word_node* pNxt;
} WORD_NODE, * PWORD_NODE;

#define PWORD_LIST PWORD_NODE

/**
 * @brief Structure to hold metrics for a single guess word, used for sorting and decision making.
 */
typedef struct _guess_metrics
{
    const char* word;
    double entropy;
    int rank;
    bool is_risky;
    char nounType;
    char verbType;
} GUESS_METRICS, * PGUESS_METRICS;

/**
 * @brief Structure to hold the final two recommended picks for one optimization path (Rank or Entropy).
 */
typedef struct _pick_data
{
    const char* word;
    const char* alternate_word;
} PICK_DATA, * PPICK_DATA;


// --- Function Prototypes ---

// Standard C/Utility Functions
void trim(char* str);
void clear_input_buffer();
int compare(const void* arg1, const void* arg2);

// Data Loading and Parsing
PWORD_ENTRY get_word_entry_from_word(const char* word, PWORD_ENTRY pDictionary, long numDictionary);
PWORD_ENTRY get_dictionary_table();
char* get_used_words_table();
PWORD_LIST get_used_words_from_webpage_string(char* pszWebPage);
char* get_used_words_webpage(void);
size_t write_callback(void* contents, size_t size, size_t nmemb, void* userp);

// Core Solver Logic
int is_good_fit(char* pMask, char notMask[6][5], char* pGood, char* pBad, char* pWord);
long filter_possible_answers(const char** pPossibleAnswers, long numCurrentAnswers, char* pMask, char notMask[6][5], char* pGood, char* pBad, long numTries);
void get_feedback_pattern(const char* guess, const char* answer, char* result_pattern);
double calculate_entropy_score(const char* guess, const char** possibleAnswers, long numPossibleAnswers);
bool is_guess_word_risky(const char* guess, char* pGood);
void get_linguistic_types(const char* word, PWORD_ENTRY pDictionary, long numDictionary, char* nounType, char* verbType, int* rank);

// Recommendation/Refactored Logic
void update_game_constraints(const char* guess, const char* result_pattern, char* pMask, char notMask[6][5], char* pGood, char* pBad, int tryIdx);
void calculate_all_metrics(PWORD_ENTRY pDictionary, const char** pPossibleAnswers, long numPossibleAnswers, char* pGood, PGUESS_METRICS pMetricsTable, long numWordsInDictionary);
bool create_and_sort_metric_buffers(PGUESS_METRICS pMetricsTable, long numPossibleAnswers, PGUESS_METRICS* ppRankSorted, PGUESS_METRICS* ppEntropySorted);
void find_top_linguistic_picks(PGUESS_METRICS pSortedMetrics, long numMetrics, PICK_DATA* pResult);
PGUESS_METRICS find_metric_by_word(const char* word, PGUESS_METRICS pArray, long num);
void print_recommendation_table(PGUESS_METRICS pRankSorted, PGUESS_METRICS pEntropySorted, long numPossibleAnswers, const PICK_DATA* pRankPicks, const PICK_DATA* pE_Picks);
void determine_final_pick(PGUESS_METRICS pRankSorted, PGUESS_METRICS pEntropySorted, long numPossibleAnswers, const PICK_DATA* rankPicks, const PICK_DATA* entropyPicks);
void analyze_and_print_recommendations(PWORD_ENTRY pDictionary, const char** pPossibleAnswers, long numPossibleAnswers, char* pGood, PGUESS_METRICS pMetricsTable);

// Comparison Functions
int sortMetricsByEntropyDescending(const void* arg1, const void* arg2);
int sortMetricsByRankDescending(const void* arg1, const void* arg2);
void printfDebug(const char* format, ...);


// --- Function Implementations ---

/**
 * @brief Prints a debug message if global conditions are met.
 * @param format The format string.
 * @param ... The arguments for the format string.
 */
void printfDebug(const char* format, ...)
{
    if (DEBUG_ON && (g_tryIdx >= DEBUG_LEVEL))
    {
        va_list args;
        va_start(args, format);
        vprintf(format, args);
        va_end(args);
    }
}

/**
 * @brief Comparison function to sort GUESS_METRICS structures by Entropy (descending),
 * with Rank (descending) as a tie-breaker.
 * @return -1 if p1 is better, 1 if p2 is better, 0 if equal.
 */
int sortMetricsByEntropyDescending(const void* arg1, const void* arg2)
{
    PGUESS_METRICS p1 = (PGUESS_METRICS)arg1;
    PGUESS_METRICS p2 = (PGUESS_METRICS)arg2;

    // Primary sort: Entropy (Highest H first)
    if (FLOAT_GREATER(p1->entropy, p2->entropy)) return -1;
    if (FLOAT_GREATER(p2->entropy, p1->entropy)) return 1;

    // Tie-breaker: Rank (HIGHER rank number is better/more frequent)
    return (p2->rank - p1->rank);
}

/**
 * @brief Comparison function to sort GUESS_METRICS structures by Rank (descending),
 * with Entropy (descending) as a tie-breaker.
 * @return -1 if p1 is better, 1 if p2 is better, 0 if equal.
 */
int sortMetricsByRankDescending(const void* arg1, const void* arg2)
{
    PGUESS_METRICS p1 = (PGUESS_METRICS)arg1;
    PGUESS_METRICS p2 = (PGUESS_METRICS)arg2;

    // Primary sort: Rank (HIGHEST numerical rank first/Descending)
    if (p2->rank > p1->rank) return 1;
    if (p1->rank > p2->rank) return -1;

    // Tie-breaker: Entropy (highest H is better)
    if (FLOAT_GREATER(p1->entropy, p2->entropy)) return -1;
    if (FLOAT_GREATER(p2->entropy, p1->entropy)) return 1;

    return 0;
}

/**
 * @brief Removes leading and trailing whitespace from a string.
 * @param str The string to trim.
 */
void trim(char* str)
{
    char* ptrToWhereNullCharShouldGo = str;
    char* currentPtr = str;
    while (*currentPtr != '\0')
    {
        char ch = *currentPtr++;
        if (ch != ' ' && ch != '\t' && ch != '\n' && ch != '\r')
        {
            ptrToWhereNullCharShouldGo = currentPtr;
        }
    }
    *ptrToWhereNullCharShouldGo = '\0';
}

/**
 * @brief Clears the standard input buffer (required after using fgets).
 */
void clear_input_buffer()
{
    int c;
    while ((c = getchar()) != '\n' && c != EOF) {}
}

/**
 * @brief Comparison function for qsort/bsearch, comparing 5-letter words alphabetically.
 * @return Standard `memcmp` result.
 */
int compare(const void* arg1, const void* arg2)
{
    return memcmp(arg1, arg2, WORD_SIZE);
}

/**
 * @brief Searches the dictionary array for a given word using binary search.
 * @param word The word to search for.
 * @param pDictionary The sorted array of word entries.
 * @param numDictionary The number of entries in the dictionary.
 * @return PWORD_ENTRY Pointer to the found entry, or NULL if not found.
 */
PWORD_ENTRY get_word_entry_from_word(const char* word, PWORD_ENTRY pDictionary, long numDictionary)
{
    return (PWORD_ENTRY)bsearch(word, pDictionary, numDictionary, sizeof(WORD_ENTRY), compare);
}

/**
 * @brief cURL callback function to dynamically grow and store downloaded data.
 * @return The size of the data successfully handled.
 */
size_t write_callback(void* contents, size_t size, size_t nmemb, void* userp)
{
    size_t realsize = size * nmemb;
    char** memory = (char**)userp;

    if (*memory == NULL)
    {
        *memory = (char*)malloc(realsize + 1);
        if (*memory == NULL) return 0;
        memcpy(*memory, contents, realsize);
        (*memory)[realsize] = '\0';
    }
    else
    {
        size_t current_size = strlen(*memory);
        char* ptr = (char*)realloc(*memory, current_size + realsize + 1);
        if (ptr == NULL) return 0;

        *memory = ptr;
        memcpy(&((*memory)[current_size]), contents, realsize);
        (*memory)[current_size + realsize] = '\0';
    }
    return realsize;
}

/**
 * @brief Downloads the webpage containing the past Wordle answers using cURL.
 * @return A pointer to the downloaded HTML content string, or NULL on failure.
 */
char* get_used_words_webpage(void)
{
    CURL* curl;
    CURLcode res;
    char* hugeBuffer = NULL;

    curl_global_init(CURL_GLOBAL_DEFAULT);
    curl = curl_easy_init();

    if (curl)
    {
        // Set the target URL
        curl_easy_setopt(curl, CURLOPT_URL, "https://www.rockpapershotgun.com/wordle-past-answers");
        // Set the callback function to handle downloaded data
        curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, write_callback);
        // Pass the address of hugeBuffer to the callback
        curl_easy_setopt(curl, CURLOPT_WRITEDATA, (void*)&hugeBuffer);
        // Follow redirects
        curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
        // Identify the client
        curl_easy_setopt(curl, CURLOPT_USERAGENT, "Chrome");

        res = curl_easy_perform(curl);

        if (res != CURLE_OK)
        {
            fprintf(stderr, "cURL failed: %s\n", curl_easy_strerror(res));
            if (hugeBuffer) free(hugeBuffer);
            hugeBuffer = NULL;
        }
        curl_easy_cleanup(curl);
    }
    curl_global_cleanup();

    if (hugeBuffer == NULL)
    {
        fprintf(stderr, "Failed to download webpage content.\n");
    }
    else
    {
        printf("Webpage content downloaded successfully.\n");
    }
    return hugeBuffer;
}

/**
 * @brief Processes the HTML content to extract the list of past Wordle answers.
 * Words flagged in g_wordle_replay_words are excluded from this list.
 * @param pszWebPage The downloaded HTML content string.
 * @return PWORD_LIST A linked list of used words to be excluded from the answer set.
 */
PWORD_LIST get_used_words_from_webpage_string(char* pszWebPage)
{
    PWORD_LIST pTop = NULL;
    PWORD_NODE* ppNextNew = &pTop;
    PWORD_NODE pNew;

    char* pTmp;
    const char* sectionHeader = "<h2>All Wordle answers</h2>";
    const char* wordStartTag = "<li>";
    const char* wordEndTag = "</li>";
    const char* listEndTag = "</ul>";
    const char* nonWordChars = " \t\n\r\v";

    numUsedWords = 0;

    // Locate the section containing the Wordle answers
    pTmp = strstr(pszWebPage, sectionHeader);
    if (pTmp == NULL) { return NULL; }
    pTmp = strstr(pTmp, wordStartTag);
    if (pTmp == NULL) { return NULL; }

    char* pListEnd = strstr(pTmp, listEndTag);
    if (pListEnd == NULL) { pListEnd = pTmp + strlen(pTmp); }

    while (pTmp != NULL && pTmp < pListEnd)
    {
        pTmp += strlen(wordStartTag);
        pTmp += strspn(pTmp, nonWordChars);

        char* pWordEndTag = strstr(pTmp, wordEndTag);
        if (pWordEndTag == NULL || pWordEndTag >= pListEnd) break;

        // Skip potential HTML tags within list items
        if (*pTmp == '<')
        {
            char* pContentStart = strchr(pTmp, '>');
            if (pContentStart != NULL && pContentStart < pWordEndTag) { pTmp = pContentStart + 1; }
        }

        pTmp += strspn(pTmp, nonWordChars);

        // Check if the content is a 5-letter word
        size_t wordLen = 0;
        while (wordLen < WORD_SIZE && isalpha((unsigned char)*(pTmp + wordLen))) { wordLen++; }

        if (wordLen == WORD_SIZE)
        {
            bool skip_word = false;

#ifdef NUM_REPLAY_WORDS
            // Check against the replay list
            for (int i = 0; i < NUM_REPLAY_WORDS && skip_word == false; i++)
            {
                if (strncmp(pTmp, g_wordle_replay_words[i], WORD_SIZE) == 0)
                {
                    skip_word = true;
                }
            }
#endif

            // If the word is NOT in the replay list, add it to the exclusion list (pTop)
            if (!skip_word)
            {
                pNew = (PWORD_NODE)malloc(sizeof(WORD_NODE));
                if (pNew == NULL) { fprintf(stderr, "Out of memory!\n"); return NULL; }
                memset(pNew, 0, sizeof(WORD_NODE));

                // Copy and uppercase the word
                memcpy(pNew->word, pTmp, WORD_SIZE);
                for (int i = 0; i < WORD_SIZE; i++)
                {
                    pNew->word[i] = toupper((unsigned char)pNew->word[i]);
                }
                pNew->word[WORD_SIZE] = '\0';

                numUsedWords++;
                *ppNextNew = pNew;
                ppNextNew = &(pNew->pNxt);
            }
        }

        // Move pointer to the start of the next list item
        char* pNextListItem = strstr(pTmp + 1, wordStartTag);
        char* pEndList = strstr(pTmp + 1, listEndTag);

        if (pNextListItem != NULL && (pEndList == NULL || pNextListItem < pEndList))
        {
            pTmp = pNextListItem;
        }
        else if (pEndList != NULL)
        {
            pTmp = pEndList;
        }
        else
        {
            pTmp = NULL;
        }
    }

    printf("Found %ld total used words (excluding replay words).\n", numUsedWords);
    return(pTop);
}


/**
 * @brief Fetches and loads the local dictionary file into memory.
 * The dictionary is loaded into a contiguous array of WORD_ENTRY structures and sorted.
 * @return PWORD_ENTRY Pointer to the allocated dictionary array, or NULL on failure.
 */
PWORD_ENTRY get_dictionary_table()
{
    FILE* fpIn;
    errno_t errval;
    char buffer[100];
    numWordsInDictionary = 0;

    PWORD_ENTRY pDictionary = (PWORD_ENTRY)malloc(sizeof(WORD_ENTRY) * maxDictionary);
    if (pDictionary == NULL)
    {
        fprintf(stderr, "Out of memory allocating dictionary!\n");
        return NULL;
    }

    // Hardcoded path to the dictionary file
    errval = fopen_s(&fpIn, "C:\\VS2022.Projects\\StuffForWordle\\WordleWordsCSVs\\AllWords.txt", "r");
    if (fpIn == NULL || errval != 0)
    {
        fprintf(stderr, "Could not open consolidated dictionary file (AllWords.txt)! Check the hardcoded path.\n");
        free(pDictionary);
        return NULL;
    }

    // Read the file line by line, parsing the word, rank, and linguistic types
    while (fgets(buffer, 100, fpIn) != NULL && numWordsInDictionary < maxDictionary)
    {
        trim(buffer);

        // Line format: [5-Letter Word][3-Digit Rank][Noun Type][Verb Type] (min 10 chars)
        if (strlen(buffer) >= 10)
        {
            PWORD_ENTRY pEntry = pDictionary + numWordsInDictionary;

            // 1. Extract and format the word (first 5 characters)
            memcpy(pEntry->word, buffer, WORD_SIZE);
            for (int i = 0; i < WORD_SIZE; i++)
            {
                pEntry->word[i] = toupper((unsigned char)pEntry->word[i]);
            }
            pEntry->word[WORD_SIZE] = '\0';

            // 2. Extract and parse the rank (next 3 characters: 000-100)
            char rankStr[4];
            memcpy(rankStr, buffer + 5, 3);
            rankStr[3] = '\0';
            pEntry->rank = atoi(rankStr);

            // 3. Extract linguistic types (next 2 characters)
            pEntry->nounType = buffer[8];
            pEntry->verbType = buffer[9];

            numWordsInDictionary++;
        }
    }

    fclose(fpIn);
    printf("Loaded %ld words from the new consolidated dictionary.\n", numWordsInDictionary);
    // Sort the dictionary for efficient O(log N) binary search access
    qsort(pDictionary, numWordsInDictionary, sizeof(WORD_ENTRY), compare);

    return pDictionary;
}

/**
 * @brief Fetches the list of previously used Wordle answers, processes the linked list,
 * and stores them in a sorted contiguous array for fast lookup.
 * @return char* Pointer to the allocated, sorted array of used words (packed 5-char strings).
 */
char* get_used_words_table()
{
    char* pUsedWords_webpage = NULL;
    PWORD_LIST pUsedWords = NULL;
    PWORD_NODE pWord = NULL;
    char* pTable = NULL;
    long cnt = 0;

    pUsedWords_webpage = get_used_words_webpage();

    if (pUsedWords_webpage != NULL)
    {
        // Parse the HTML content into a linked list of words
        pUsedWords = get_used_words_from_webpage_string(pUsedWords_webpage);
        free(pUsedWords_webpage);

        if (pUsedWords != NULL)
        {
            // Allocate space for a contiguous array of 5-char words
            pTable = (char*)malloc(WORD_SIZE * numUsedWords);
            if (pTable == NULL)
            {
                fprintf(stderr, "Out of memory allocating used word table\n");
                return NULL;
            }

            // Copy words from linked list to the contiguous array and free list nodes
            pWord = pUsedWords;
            while (pWord != NULL)
            {
                PWORD_NODE pTemp = pWord->pNxt;

                memcpy(pTable + (cnt * WORD_SIZE), pWord->word, WORD_SIZE);
                free(pWord);
                pWord = pTemp;
                cnt++;
            }
        }
    }

    if (pTable != NULL)
    {
        // Sort the list of used words for efficient O(log N) exclusion check
        qsort(pTable, numUsedWords, WORD_SIZE, compare);
    }
    else // Ensure pTable is not NULL if no words were found
    {
        pTable = (char*)malloc(1);
        numUsedWords = 0;
    }

    return pTable;
}

/**
 * @brief Checks if a given word is a valid remaining answer based on current game constraints.
 * @param pMask Mask of known green letters (e.g., "*A*S*").
 * @param notMask Array of letters that cannot be in specific positions (from yellow and black results).
 * @param pGood String of required letters (min count constraint, from yellow and green results).
 * @param pBad String of letters that must be completely absent (from black results).
 * @param pWord The word being checked against the constraints.
 * @return 1 if the word is a good fit, 0 otherwise.
 */
int is_good_fit(char* pMask, char notMask[6][5], char* pGood, char* pBad, char* pWord)
{
    // 1. CHECK REQUIRED LETTER COUNTS (YELLOW AND GREEN)
    int required_counts[26] = { 0 };
    for (char* p = pGood; *p != '\0'; p++)
    {
        required_counts[*p - 'A']++;
    }

    for (int i = 0; i < 26; i++)
    {
        if (required_counts[i] > 0)
        {
            char required_char = 'A' + i;
            int word_count = 0;

            for (int wordIdx = 0; wordIdx < WORD_SIZE; wordIdx++)
            {
                if (*(pWord + wordIdx) == required_char)
                {
                    word_count++;
                }
            }

            // Word must contain at least the minimum required count of the letter
            if (word_count < required_counts[i])
            {
                return 0;
            }
        }
    }

    // 2. CHECK POSITIONAL CONSTRAINTS
    for (int idx = 0; (idx < WORD_SIZE); idx++)
    {
        char theChar = *(pWord + idx);

        // Must not contain any "black-listed" letters (pBad)
        if (strchr(pBad, theChar) != NULL) return 0;

        // Must match green letter mask (pMask)
        if (*(pMask + idx) != '*' && *(pMask + idx) != theChar) return 0;

        // Must not have a yellow letter in the known incorrect position (notMask)
        for (int notIdx = 0; notIdx < 6; notIdx++)
        {
            if (notMask[notIdx][idx] == theChar) return 0;
        }
    }

    return 1;
}

/**
 * @brief Looks up and returns the linguistic types and rank for a word from the dictionary.
 * @param word The word to look up.
 * @param pDictionary The dictionary array.
 * @param numDictionary The size of the dictionary.
 * @param nounType Output pointer for noun type ('P', 'S', 'N').
 * @param verbType Output pointer for verb type ('T', 'S', 'P', 'N').
 * @param rank Output pointer for the word rank (0-100).
 */
void get_linguistic_types(const char* word, PWORD_ENTRY pDictionary, long numDictionary, char* nounType, char* verbType, int* rank)
{
    PWORD_ENTRY pFound = get_word_entry_from_word(word, pDictionary, numDictionary);
    if (pFound)
    {
        *nounType = pFound->nounType;
        *verbType = pFound->verbType;
        *rank = pFound->rank;
    }
    else
    {
        // Default values for words not found in the linguistic dictionary
        *nounType = 'N';
        *verbType = 'N';
        *rank = 0;
    }
}

/**
 * @brief Calculates the Wordle feedback pattern (G, Y, B) for a hypothetical guess/answer pair.
 * This simulates the core Wordle logic needed for entropy calculation.
 * @param guess The word being guessed.
 * @param answer The actual solution word.
 * @param result_pattern Output buffer for the 5-character result pattern (e.g., "BGYBB").
 */
void get_feedback_pattern(const char* guess, const char* answer, char* result_pattern)
{
    memset(result_pattern, 'B', WORD_SIZE);
    result_pattern[WORD_SIZE] = '\0';

    int answer_char_counts[26] = { 0 };
    bool guess_used[WORD_SIZE] = { false };

    // 1. Determine Green ('G') matches and tally remaining answer letters
    for (int i = 0; i < WORD_SIZE; i++)
    {
        if (guess[i] == answer[i])
        {
            result_pattern[i] = 'G';
            guess_used[i] = true;
        }
        else
        {
            answer_char_counts[answer[i] - 'A']++;
        }
    }

    // 2. Determine Yellow ('Y') matches
    for (int i = 0; i < WORD_SIZE; i++)
    {
        if (result_pattern[i] != 'G')
        {
            int letter_index = guess[i] - 'A';
            if (answer_char_counts[letter_index] > 0)
            {
                result_pattern[i] = 'Y';
                // Decrement count to handle duplicates correctly
                answer_char_counts[letter_index]--;
            }
        }
    }
}

/**
 * @brief Calculates the Shannon Entropy score for a word against the possible answers.
 * @param guess The word to calculate entropy for.
 * @param possibleAnswers Array of remaining possible answer words.
 * @param numPossibleAnswers The number of words in the array.
 * @return double The calculated entropy score (H).
 */
double calculate_entropy_score(const char* guess, const char** possibleAnswers, long numPossibleAnswers)
{
    double entropy = 0.0;
    char pattern[WORD_SIZE + 1];

    PWORD_LIST pPatternCounts = NULL;
    PWORD_NODE pNew = NULL;
    PWORD_NODE pCurrent;
    PWORD_NODE* ppNextNew;

    if (numPossibleAnswers <= 1) return 0.0;

    // 1. Tally the frequency of each possible result pattern
    for (long i = 0; i < numPossibleAnswers; i++)
    {
        const char* answer = possibleAnswers[i];
        get_feedback_pattern(guess, answer, pattern);

        // Search for the existing pattern in the linked list
        pCurrent = pPatternCounts;
        ppNextNew = &pPatternCounts;
        bool found = false;

        while (pCurrent != NULL)
        {
            if (strcmp(pCurrent->word, pattern) == 0)
            {
                pCurrent->rank++; // Increment count
                found = true;
                break;
            }
            ppNextNew = &(pCurrent->pNxt);
            pCurrent = pCurrent->pNxt;
        }

        // If pattern not found, create a new node
        if (!found)
        {
            pNew = (PWORD_NODE)malloc(sizeof(WORD_NODE));
            if (pNew == NULL) { fprintf(stderr, "Out of memory in entropy calculation!\n"); return 0.0; }
            memset(pNew, 0, sizeof(WORD_NODE));

            memcpy(pNew->word, pattern, WORD_SIZE + 1);
            pNew->rank = 1;

            *ppNextNew = pNew;
        }
    }

    // 2. Calculate Shannon Entropy H
    const double LOG2_E = log(2.0); // Used to convert natural log to log base 2
    pCurrent = pPatternCounts;

    while (pCurrent != NULL)
    {
        long count_k = pCurrent->rank;
        double P_k = (double)count_k / numPossibleAnswers; // Probability of pattern k

        // H = sum(P_k * log2(1/P_k))
        // log2(1/P_k) is equivalent to log(N/count_k) / log(2)
        entropy += P_k * (log((double)numPossibleAnswers / count_k) / LOG2_E);

        // Free linked list node and move to next
        PWORD_NODE pTemp = pCurrent->pNxt;
        free(pCurrent);
        pCurrent = pTemp;
    }

    return entropy;
}

/**
 * @brief Checks if a guess word contains a repeated letter that is NOT guaranteed by current constraints.
 * This guards against "risky" guesses (e.g., guessing 'DADDY' when D isn't confirmed as a double).
 * @param guess The word to check.
 * @param pGood The string of required letters (yellow or green).
 * @return true if the word has unconfirmed repeat letters, false otherwise.
 */
bool is_guess_word_risky(const char* guess, char* pGood)
{
    int guess_counts[26] = { 0 };
    int required_counts[26] = { 0 };

    // Tally letter counts in the guess word
    for (int i = 0; i < WORD_SIZE; i++)
    {
        guess_counts[guess[i] - 'A']++;
    }

    // Tally minimum required letter counts from game state (pGood)
    for (char* p = pGood; *p != '\0'; p++)
    {
        required_counts[*p - 'A']++;
    }

    for (int i = 0; i < 26; i++)
    {
        if (guess_counts[i] > 1) // Check only letters that appear multiple times in the guess
        {
            // If the number of times the letter appears in the guess is greater than
            // the confirmed required count from the board state, it is risky.
            if (guess_counts[i] > required_counts[i])
            {
                return true;
            }
        }
    }

    return false;
}

/**
 * @brief Searches an array of GUESS_METRICS structs to find the entry
 * corresponding to a specific word.
 * @param word The word to search for.
 * @param pArray The array of metrics.
 * @param num The number of elements in the array.
 * @return PGUESS_METRICS Pointer to the found metric, or NULL if not found.
 */
PGUESS_METRICS find_metric_by_word(const char* word, PGUESS_METRICS pArray, long num)
{
    if (strcmp(word, "NONE") == 0) return NULL;
    for (long i = 0; i < num; i++)
    {
        if (strcmp(pArray[i].word, word) == 0) return &pArray[i];
    }
    return NULL;
}


// --- Refactored Functions Start Here ---

/**
 * @brief Performs the constraint update logic for a single guess.
 * Calculates confirmed counts and updates the mask, required letters (pGood),
 * excluded letters (pBad), and positional exclusions (notMask).
 * @param guess The 5-letter word guessed by the user.
 * @param result_pattern The 5-char feedback (B, G, Y) from Wordle.
 * @param pMask The green letter mask.
 * @param notMask Positional exclusions array.
 * @param pGood String of required letters (min count constraint).
 * @param pBad String of letters that must be absent.
 * @param tryIdx The current turn number.
 */
void update_game_constraints(const char* guess, const char* result_pattern, char* pMask, char notMask[6][5], char* pGood, char* pBad, int tryIdx)
{
    // 1. Calculate confirmed minimum counts for required letters (Yellow/Green)
    int confirmed_counts[26] = { 0 };
    for (int idx = 0; idx < WORD_SIZE; idx++)
    {
        char current_char = toupper((unsigned char)guess[idx]);
        if (result_pattern[idx] == 'G' || result_pattern[idx] == 'Y')
        {
            confirmed_counts[current_char - 'A']++;
        }
    }

    // 2. Apply updates based on result pattern position by position
    for (int idx = 0; idx < WORD_SIZE; idx++)
    {
        char current_char = toupper((unsigned char)guess[idx]);

        // Find how many of this char are already marked as required
        int current_required_count = 0;
        for (size_t k = 0; k < strlen(pGood); k++)
        {
            if (pGood[k] == current_char) current_required_count++;
        }

        size_t len_good = strlen(pGood);
        size_t len_bad = strlen(pBad);

        if (result_pattern[idx] == 'G')
        {
            pMask[idx] = current_char;
            // Update required letters (pGood) if we found a new, necessary instance
            if (current_required_count < confirmed_counts[current_char - 'A'])
            {
                pGood[len_good] = current_char;
                pGood[len_good + 1] = '\0';
            }
        }
        else if (result_pattern[idx] == 'Y')
        {
            notMask[tryIdx - 1][idx] = current_char;
            // Update required letters (pGood)
            if (current_required_count < confirmed_counts[current_char - 'A'])
            {
                pGood[len_good] = current_char;
                pGood[len_good + 1] = '\0';
            }
        }
        else if (result_pattern[idx] == 'B')
        {
            notMask[tryIdx - 1][idx] = current_char;

            // Only blacklist the letter (pBad) if it is NOT a required letter (count is 0)
            if (current_required_count == 0)
            {
                if (strchr(pBad, current_char) == NULL)
                {
                    pBad[len_bad] = current_char;
                    pBad[len_bad + 1] = '\0';
                }
            }
        }
    }
}

/**
 * @brief Calculates all required metrics (H, R, Linguistic, Risk) for every possible answer.
 * @param pDictionary The entire word dictionary.
 * @param pPossibleAnswers Array of pointers to remaining possible answers.
 * @param numPossibleAnswers The number of words remaining.
 * @param pGood The string of required letters (for repeat risk check).
 * @param pMetricsTable The pre-allocated array to store the results.
 * @param numWordsInDictionary Total size of the dictionary (for lookup).
 */
void calculate_all_metrics(PWORD_ENTRY pDictionary, const char** pPossibleAnswers, long numPossibleAnswers, char* pGood, PGUESS_METRICS pMetricsTable, long numWordsInDictionary)
{
    for (long i = 0; i < numPossibleAnswers; i++)
    {
        const char* pWord = pPossibleAnswers[i];
        PGUESS_METRICS pMetric = pMetricsTable + i;
        char nounType, verbType;
        int rank;

        pMetric->word = pWord;

        // Calculate the core information metric
        pMetric->entropy = calculate_entropy_score(pWord, pPossibleAnswers, numPossibleAnswers);

        // Look up static metrics
        get_linguistic_types(pWord, pDictionary, numWordsInDictionary, &nounType, &verbType, &rank);
        pMetric->rank = rank;
        pMetric->nounType = nounType;
        pMetric->verbType = verbType;

        // Calculate dynamic risk based on current game state
        pMetric->is_risky = is_guess_word_risky(pWord, pGood);
    }
}

/**
 * @brief Allocates and sorts two metric buffers based on Rank and Entropy priorities.
 * The caller MUST free the memory pointed to by ppRankSorted and ppEntropySorted.
 * @param pMetricsTable The source metric table (unsorted).
 * @param numPossibleAnswers The number of elements.
 * @param ppRankSorted Output pointer for the Rank-sorted buffer.
 * @param ppEntropySorted Output pointer for the Entropy-sorted buffer.
 * @return bool True on success, false on memory allocation failure.
 */
bool create_and_sort_metric_buffers(PGUESS_METRICS pMetricsTable, long numPossibleAnswers, PGUESS_METRICS* ppRankSorted, PGUESS_METRICS* ppEntropySorted)
{
    // Allocate memory for two temporary, sortable copies
    *ppRankSorted = (PGUESS_METRICS)malloc(numPossibleAnswers * sizeof(GUESS_METRICS));
    *ppEntropySorted = (PGUESS_METRICS)malloc(numPossibleAnswers * sizeof(GUESS_METRICS));

    if (!*ppRankSorted || !*ppEntropySorted)
    {
        fprintf(stderr, "Out of memory for sort buffers!\n");
        if (*ppRankSorted) free(*ppRankSorted);
        if (*ppEntropySorted) free(*ppEntropySorted);
        return false;
    }

    // Copy the raw metric data
    memcpy(*ppRankSorted, pMetricsTable, numPossibleAnswers * sizeof(GUESS_METRICS));
    memcpy(*ppEntropySorted, pMetricsTable, numPossibleAnswers * sizeof(GUESS_METRICS));

    // Sort 1: Priority on Rank (R), secondary on Entropy (H)
    qsort(*ppRankSorted, numPossibleAnswers, sizeof(GUESS_METRICS), sortMetricsByRankDescending);

    // Sort 2: Priority on Entropy (H), secondary on Rank (R)
    qsort(*ppEntropySorted, numPossibleAnswers, sizeof(GUESS_METRICS), sortMetricsByEntropyDescending);

    return true;
}

/**
 * @brief Finds the top pick and alternate based on strict linguistic/risk preferences.
 * This filters out undesirable word forms (plurals, past tense, etc.) from the top of the sorted list.
 * @param pSortedMetrics The array sorted by the primary metric (Rank or Entropy).
 * @param numMetrics Number of entries in the array.
 * @param pResult Output structure to store the top pick and alternate.
 */
void find_top_linguistic_picks(PGUESS_METRICS pSortedMetrics, long numMetrics, PICK_DATA* pResult)
{
    pResult->word = "NONE";
    pResult->alternate_word = "NONE";
    int found_count = 0;

    // Search for the top two words that are linguistically sound and not risky
    for (long i = 0; i < numMetrics; i++)
    {
        PGUESS_METRICS pMetric = pSortedMetrics + i;

        // CRITICAL FILTER: Exclude Plural Nouns ('P'), Past Tense Verbs ('T'),
        // Third-Person Singular Verbs ('S'), and words with unconfirmed repeat letters.
        if (pMetric->nounType != 'P' && pMetric->verbType != 'T' &&
            pMetric->verbType != 'S' && pMetric->is_risky == false)
        {
            if (found_count == 0)
            {
                pResult->word = pMetric->word;
                found_count++;
            }
            else if (found_count == 1)
            {
                pResult->alternate_word = pMetric->word;
                found_count++;
                break; // Found top pick and alternate
            }
        }
    }

    // Fallback: If not enough linguistically clean words were found, use the absolute top words
    if (found_count < 2 && numMetrics > 0)
    {
        // If 0 clean words found, use absolute top word as the Top Pick
        if (found_count == 0)
        {
            pResult->word = pSortedMetrics[0].word;
            found_count = 1;
        }

        // If less than 2 clean words found, use absolute second best as Alternate (if available)
        if (found_count == 1 && numMetrics > 1)
        {
            if (strcmp(pResult->alternate_word, "NONE") == 0)
            {
                if (strcmp(pSortedMetrics[1].word, pResult->word) != 0)
                {
                    pResult->alternate_word = pSortedMetrics[1].word;
                }
            }
        }
        // If only one word total remains, alternate is NONE
        else if (numMetrics == 1)
        {
            pResult->alternate_word = "NONE";
        }
    }
}

/**
 * @brief Prints the two-column table showing the top N choices for both Rank and Entropy.
 * @param pRankSorted The array sorted by Rank.
 * @param pEntropySorted The array sorted by Entropy.
 * @param numPossibleAnswers The total number of words.
 * @param pRankPicks The final top picks for the Rank path.
 * @param pE_Picks The final top picks for the Entropy path.
 */
void print_recommendation_table(PGUESS_METRICS pRankSorted, PGUESS_METRICS pEntropySorted, long numPossibleAnswers, const PICK_DATA* pRankPicks, const PICK_DATA* pE_Picks)
{
    const int COL_WIDTH = 43;
    const int MAX_ROWS = MAX_TOP_PICKS;

    printf("\n%*s--- Top %d Choices (Possible Answers: %ld) ---\n", 22, "", MAX_ROWS, numPossibleAnswers);
    printf("%*s(R=Rank, H=Entropy, N=Plurality, V=Preterite, R=Repeat Risk)\n", 16, "");
    printf("-------------------------------------------+-------------------------------------------\n");
    printf("     Rank-Optimized                        |     Entropy-Optimized                     \n");
    printf("   (Higher Rank = More Common)             |   (Higher H = Reduces solution set)       \n");
    printf("-------------------------------------------+-------------------------------------------\n");

    // Print the top N rows side-by-side
    for (int i = 0; i < MAX_ROWS && i < numPossibleAnswers; i++)
    {
        PGUESS_METRICS pR = pRankSorted + i;
        PGUESS_METRICS pE = pEntropySorted + i;

        char rank_col_buffer[200];
        char entropy_col_buffer[200];

        // Format Left Column - Word (R, H) N=x V=x R=Y/N
        sprintf_s(rank_col_buffer, sizeof(rank_col_buffer), "%3d. %-5s (R=%03d, H=%.4f) N=%c V=%c R=%c",
            i + 1, pR->word, pR->rank, pR->entropy, pR->nounType, pR->verbType,
            (pR->is_risky ? 'Y' : 'N'));

        // Format Right Column - Word (R, H) N=x V=x R=Y/N
        sprintf_s(entropy_col_buffer, sizeof(entropy_col_buffer), "%3d. %-5s (R=%03d, H=%.4f) N=%c V=%c R=%c",
            i + 1, pE->word, pE->rank, pE->entropy, pE->nounType, pE->verbType,
            (pE->is_risky ? 'Y' : 'N'));

        printf("%-*s|%-*s\n", COL_WIDTH, rank_col_buffer, COL_WIDTH, entropy_col_buffer);
    }

    printf("-------------------------------------------+-------------------------------------------\n");

    // Lookup metrics for the final determined picks (after linguistic filtering)
    PGUESS_METRICS pR_Pick = find_metric_by_word(pRankPicks->word, pRankSorted, numPossibleAnswers);
    PGUESS_METRICS pE_Pick = find_metric_by_word(pE_Picks->word, pEntropySorted, numPossibleAnswers);
    PGUESS_METRICS pR_Alt = find_metric_by_word(pRankPicks->alternate_word, pRankSorted, numPossibleAnswers);
    PGUESS_METRICS pE_Alt = find_metric_by_word(pE_Picks->alternate_word, pEntropySorted, numPossibleAnswers);

    char rank_pick_buffer[100], rank_alt_buffer[100];
    char entropy_pick_buffer[100], entropy_alt_buffer[100];

    // Format Top Pick (Rank-Optimized)
    sprintf_s(rank_pick_buffer, sizeof(rank_pick_buffer), "     Top Pick  : %-5s (R=%03d, H=%.4f)",
        pRankPicks->word, pR_Pick ? pR_Pick->rank : 0, pR_Pick ? pR_Pick->entropy : 0.0);

    // Format Alternate (Rank-Optimized)
    sprintf_s(rank_alt_buffer, sizeof(rank_alt_buffer), "     Alternate : %-5s (R=%03d, H=%.4f)",
        pRankPicks->alternate_word, pR_Alt ? pR_Alt->rank : 0, pR_Alt ? pR_Alt->entropy : 0.0);

    // Format Top Pick (Entropy-Optimized)
    sprintf_s(entropy_pick_buffer, sizeof(entropy_pick_buffer), "     Top Pick  : %-5s (R=%03d, H=%.4f)",
        pE_Picks->word, pE_Pick ? pE_Pick->rank : 0, pE_Pick ? pE_Pick->entropy : 0.0);

    // Format Alternate (Entropy-Optimized)
    sprintf_s(entropy_alt_buffer, sizeof(entropy_alt_buffer), "     Alternate : %-5s (R=%03d, H=%.4f)",
        pE_Picks->alternate_word, pE_Alt ? pE_Alt->rank : 0, pE_Alt ? pE_Alt->entropy : 0.0);

    printf("%-*s|%-*s\n", COL_WIDTH, rank_pick_buffer, COL_WIDTH, entropy_pick_buffer);
    printf("%-*s|%-*s\n", COL_WIDTH, rank_alt_buffer, COL_WIDTH, entropy_alt_buffer);

    printf("-------------------------------------------+-------------------------------------------\n");
}

/**
 * @brief Applies the dynamic H/R trade-off logic to select the single best final recommendation.
 * Prints the final top pick in a centered banner format.
 * @param pRankSorted The Rank-sorted array (for absolute top pick in small sets).
 * @param pEntropySorted The Entropy-sorted array (for metrics).
 * @param numPossibleAnswers The number of words remaining.
 * @param rankPicks The top picks from the Rank path.
 * @param entropyPicks The top picks from the Entropy path.
 */
void determine_final_pick(PGUESS_METRICS pRankSorted, PGUESS_METRICS pEntropySorted, long numPossibleAnswers, const PICK_DATA* rankPicks, const PICK_DATA* entropyPicks)
{
    // Retrieve metrics for the linguistically filtered top picks
    PGUESS_METRICS pR_Pick = find_metric_by_word(rankPicks->word, pRankSorted, numPossibleAnswers);
    PGUESS_METRICS pE_Pick = find_metric_by_word(entropyPicks->word, pEntropySorted, numPossibleAnswers);

    // Default to the Rank pick (most common)
    const char* final_word = rankPicks->word;
    double final_rank = pR_Pick ? pR_Pick->rank : 0.0;
    double final_entropy = pR_Pick ? pR_Pick->entropy : 0.0;

    if (pR_Pick && pE_Pick)
    {
        double entropy_diff = fabs(pE_Pick->entropy - pR_Pick->entropy);

        if (numPossibleAnswers > LOW_POSSIBLE_ANSWER_COUNT)
        {
            // Large set (N > 25): Prioritize H unless the difference is negligible.
            if (entropy_diff > ENTROPY_RANK_THRESHOLD)
            {
                // Difference is significant: choose Entropy pick for max information gain
                final_word = pE_Pick->word;
                final_rank = pE_Pick->rank;
                final_entropy = pE_Pick->entropy;
            }
            // Otherwise, Rank-Pick (default) is used for its higher probability.
        }
        else // Small set (N <= 25): Prioritize Rank.
        {
            // Choose the absolute highest ranked word (first in the pRankSorted list)
            final_word = pRankSorted[0].word;
            final_rank = pRankSorted[0].rank;
            final_entropy = pRankSorted[0].entropy;
        }
    }
    else if (numPossibleAnswers > 0)
    {
        // Fallback: If filtering removed one of the key picks, use the absolute highest Rank word.
        final_word = pRankSorted[0].word;
        final_rank = pRankSorted[0].rank;
        final_entropy = pRankSorted[0].entropy;
    }

    // Format the final recommendation banner
    char final_pick_buffer[100];
    sprintf_s(final_pick_buffer, sizeof(final_pick_buffer), "Final Top Pick: %s (R=%03d, H=%.4f)",
        final_word, (int)final_rank, final_entropy);

    // Print centered final pick
    int final_string_length = strlen(final_pick_buffer);
    int total_width = 89;
    int padding = (total_width - final_string_length) / 2;

    printf("%*s%s%*s\n", padding, "", final_pick_buffer, padding, "");
    printf("---------------------------------------------------------------------------------------\n");
}


/**
 * @brief Coordinates the metric calculation, sorting, filtering, and printing for a single turn.
 * @param pDictionary The entire word dictionary.
 * @param pPossibleAnswers Array of pointers to remaining possible answers.
 * @param numPossibleAnswers The number of words remaining.
 * @param pGood The string of required letters (for repeat risk check).
 * @param pMetricsTable The pre-allocated array for metric storage.
 */
void analyze_and_print_recommendations(PWORD_ENTRY pDictionary, const char** pPossibleAnswers, long numPossibleAnswers, char* pGood, PGUESS_METRICS pMetricsTable)
{
    PGUESS_METRICS pRankSorted = NULL;
    PGUESS_METRICS pEntropySorted = NULL;
    PICK_DATA rankPicks;
    PICK_DATA entropyPicks;

    if (numPossibleAnswers == 0) return;

    // 1. Calculate all metrics (H, R, Linguistic, Risk) for the current possible answers
    calculate_all_metrics(pDictionary, pPossibleAnswers, numPossibleAnswers, pGood, pMetricsTable, numWordsInDictionary);

    // 2. Create and sort two separate metric buffers (must free these later)
    if (!create_and_sort_metric_buffers(pMetricsTable, numPossibleAnswers, &pRankSorted, &pEntropySorted)) return;

    // 3. Find Top Pick and Alternate for each path, applying linguistic/risk filters
    find_top_linguistic_picks(pRankSorted, numPossibleAnswers, &rankPicks);
    find_top_linguistic_picks(pEntropySorted, numPossibleAnswers, &entropyPicks);

    // 4. Print the detailed two-column recommendation table
    print_recommendation_table(pRankSorted, pEntropySorted, numPossibleAnswers, &rankPicks, &entropyPicks);

    // 5. Determine and print the final top pick based on the dynamic H/R trade-off
    determine_final_pick(pRankSorted, pEntropySorted, numPossibleAnswers, &rankPicks, &entropyPicks);

    // 6. Cleanup
    free(pRankSorted);
    free(pEntropySorted);
}


/**
 * @brief Filters the list of possible answers based on the latest game constraints.
 * This function updates the array of possible answers in place by moving valid pointers
 * to the beginning of the array.
 * @param pPossibleAnswers Array of pointers to remaining possible answers.
 * @param numCurrentAnswers The current count of answers.
 * @param pMask Green letters mask.
 * @param notMask Positional exclusions (Yellow/Black).
 * @param pGood Required letters (Min Count).
 * @param pBad Letters that must be absent.
 * @param numTries Current attempt number (unused but kept for context).
 * @return long The new count of possible answers.
 */
long filter_possible_answers(const char** pPossibleAnswers, long numCurrentAnswers, char* pMask, char notMask[6][5], char* pGood, char* pBad, long numTries)
{
    long numNewAnswers = 0;

    for (long i = 0; i < numCurrentAnswers; i++)
    {
        char* pWord = (char*)pPossibleAnswers[i];
        if (is_good_fit(pMask, notMask, pGood, pBad, pWord))
        {
            // Keep the pointer by moving it to the front of the array
            pPossibleAnswers[numNewAnswers++] = pWord;
        }
    }

    printf("\nFiltered. %ld possible answers remain.\n", numNewAnswers);
    return numNewAnswers;
}

/**
 * @brief Main function to initialize data, run the solver loop, and manage resources.
 */
int main(int argc, char* argv[])
{
    int result = 0;
    char* pUsedWordsTable = NULL;
    PWORD_ENTRY pDictionaryTable = NULL;

    char** pPossibleAnswers = NULL;
    long numPossibleAnswers = 0;
    PGUESS_METRICS pMetricsTable = NULL;

    // Game state constraint buffers
    char mask[WORD_SIZE + 1];
    char goodButDontKnowWhere[WORD_SIZE + 1];
    char cannotHave[26];
    char notMask[6][WORD_SIZE];
    char result_input[WORD_SIZE + 1];

    // --- 1. Initialization ---
    memset(mask, '*', WORD_SIZE);
    mask[WORD_SIZE] = '\0'; // Green mask initialized to *****
    memset(goodButDontKnowWhere, 0, sizeof(goodButDontKnowWhere)); // Required letters initialized empty
    memset(cannotHave, 0, sizeof(cannotHave)); // Excluded letters initialized empty
    for (int idx = 0; idx < 6; idx++)
    {
        memcpy(notMask[idx], mask, WORD_SIZE); // Positional exclusions initialized to *
    }
    result_input[WORD_SIZE] = '\0';


    // --- 2. Data Loading ---
    pUsedWordsTable = get_used_words_table();
    pDictionaryTable = get_dictionary_table();

    if (pDictionaryTable == NULL)
    {
        fprintf(stderr, "Fatal Error: Dictionary could not be loaded. Exiting.\n");
        goto end_game_loop;
    }

    // Allocate memory for the list of pointers to possible answers and the metrics work buffer
    pPossibleAnswers = (char**)malloc(numWordsInDictionary * sizeof(char*));
    pMetricsTable = (PGUESS_METRICS)malloc(numWordsInDictionary * sizeof(GUESS_METRICS));

    if (pPossibleAnswers == NULL || pMetricsTable == NULL) { fprintf(stderr, "Out of memory for answer list/metrics table!\n"); goto end_game_loop; }

    // Populate the initial list of possible answers (dictionary minus used words)
    for (long i = 0; i < numWordsInDictionary; i++)
    {
        char* pWord = pDictionaryTable[i].word;
        // Check if the word is NOT in the list of past used words
        if (bsearch(pWord, pUsedWordsTable, numUsedWords, WORD_SIZE, compare) == NULL)
        {
            pPossibleAnswers[numPossibleAnswers++] = pWord;
        }
    }

    g_tryIdx = 1;

    // Print initial recommendations (Turn 1)
    analyze_and_print_recommendations(pDictionaryTable, (const char**)pPossibleAnswers, numPossibleAnswers, goodButDontKnowWhere, pMetricsTable);
    printf("It is recommended you enter one of these words first.\n");


    // --- 3. Main Game Loop ---
    for (g_tryIdx = 1; g_tryIdx <= 6; g_tryIdx++)
    {
        char buffer[2048];
        printf("\n--- Turn %d of 6 ---\n", g_tryIdx);

        // A. Get User Guess Input
        printf("Enter your 5-letter word guess: ");
        if (fgets(buffer, 100, stdin) == NULL) break;
        trim(buffer);
        if (strcmp(buffer, "q") == 0) break;
        if (strlen(buffer) != WORD_SIZE)
        {
            printf("You must enter 5 letters. Try again!\n");
            g_tryIdx--;
            continue;
        }

        // B. Get Result Pattern Input (Validation loop)
        while (1)
        {
            printf("Enter the 5-character result (B=Black/Gray, G=Green, Y=Yellow) e.g. 'BGYBB': ");
            if (fgets(result_input, sizeof(result_input), stdin) == NULL) goto end_game_loop;
            trim(result_input);
            clear_input_buffer();

            bool valid = true;
            for (int i = 0; i < WORD_SIZE; i++)
            {
                result_input[i] = toupper((unsigned char)result_input[i]);
                if (result_input[i] != 'B' && result_input[i] != 'G' && result_input[i] != 'Y')
                {
                    printf("Invalid character '%c'. Please use only B, G, or Y.\n", result_input[i]);
                    valid = false;
                    break;
                }
            }
            if (valid) break;
        }

        // C. Update all game constraints based on guess and result
        update_game_constraints(buffer, result_input, mask, notMask, goodButDontKnowWhere, cannotHave, g_tryIdx);

        printf("\n--- Current Game State ---\n");
        printf("Mask (Green) : %-5.5s\n", mask);
        printf("Required Letters: %-5.5s (Min Count Constraint)\n", goodButDontKnowWhere);
        printf("Excluded Letters: %s\n", cannotHave);

        // D. Check for Solution
        if (strchr(mask, '*') == NULL)
        {
            printf("\n*** SOLVED! The word is %s ***\n", mask);
            break;
        }

        // E. Filter and Analyze
        numPossibleAnswers = filter_possible_answers((const char**)pPossibleAnswers, numPossibleAnswers, mask, notMask, goodButDontKnowWhere, cannotHave, g_tryIdx);

        if (numPossibleAnswers > 0)
        {
            analyze_and_print_recommendations(pDictionaryTable, (const char**)pPossibleAnswers, numPossibleAnswers, goodButDontKnowWhere, pMetricsTable);

            if (numPossibleAnswers == 1)
            {
                printf("\n*** SOLUTION IDENTIFIED: %s ***\n", (char*)pPossibleAnswers[0]);
                break;
            }
        }
        else
        {
            printf("\n*** ERROR: No possible words remain. Check your input! ***\n");
            break;
        }
    }

end_game_loop:
    // --- 4. Resource Cleanup ---
    if (pMetricsTable) free(pMetricsTable);
    if (pPossibleAnswers) free(pPossibleAnswers);
    if (pDictionaryTable) free(pDictionaryTable);
    if (pUsedWordsTable) free(pUsedWordsTable);

    return(result);
}
