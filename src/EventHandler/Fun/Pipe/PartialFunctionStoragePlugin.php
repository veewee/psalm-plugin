<?php
declare(strict_types=1);

namespace Psl\Psalm\EventHandler\Fun\Pipe;

use PhpParser;
use PhpParser\Node\Expr;
use Psalm\Codebase;
use Psalm\Internal\Analyzer\StatementsAnalyzer;
use Psalm\Internal\Type\TemplateInferredTypeReplacer;
use Psalm\Internal\Type\TemplateResult;
use Psalm\Plugin\DynamicFunctionStorage;
use Psalm\Plugin\DynamicTemplateProvider;
use Psalm\Plugin\EventHandler\DynamicFunctionStorageProviderInterface;
use Psalm\Plugin\EventHandler\Event\DynamicFunctionStorageProviderEvent;
use Psalm\StatementsSource;
use Psalm\Storage\FunctionLikeParameter;
use Psalm\Storage\FunctionLikeStorage;
use Psalm\Type\Union;
use Psalm\Type;

class PartialFunctionStoragePlugin implements DynamicFunctionStorageProviderInterface
{
    public static function getFunctionIds(): array
    {
        return [
            strtolower('Psl\\Fun\\partial_left'),
            strtolower('Psl\\Fun\\partial_right'),
        ];
    }

    public static function getFunctionStorage(DynamicFunctionStorageProviderEvent $event): ?DynamicFunctionStorage
    {
        $args = $event->getArgs();
        $all_args_count = count($args);
        $fixed_args_count = $all_args_count - 1;
        $template_provider = $event->getTemplateProvider();
        $source = $event->getStatementSource();
        $codebase = $event->getCodebase();

        if ($all_args_count < 2) {
            return null;
        }

        $partial_function_storage = self::getPartialFunctionStorage($source, $args[0]->value);

        if (null === $partial_function_storage) {
            return null;
        }

        $mapped_template_result = self::getMappedLowerBounds($template_provider, $partial_function_storage);
        $mapped_param_types = self::mapParamTypes($codebase, $partial_function_storage, $mapped_template_result);
        $mapped_return_type = self::mapReturnType($codebase, $partial_function_storage, $mapped_template_result);

        $is_partial_left = $event->getFunctionId() === strtolower('Psl\\Fun\\partial_left');

        $fixed_params = self::toParamList(
            $is_partial_left
                ? array_slice($mapped_param_types, 0, $fixed_args_count)
                : array_slice($mapped_param_types, $fixed_args_count)
        );

        $rest_params = self::toParamList(
            $is_partial_left
                ? array_slice($mapped_param_types, $fixed_args_count)
                : array_slice($mapped_param_types, 0, $fixed_args_count)
        );

        // First arg of function should be generic closure (first-class-callable map(...) or old way callable 'map')
        // But rest args already inferred, and it has no sense. We can leave just TCallable.
        $partial_function_param = new FunctionLikeParameter(
            'partial_function',
            false,
            new Type\Union([
                new Type\Atomic\TCallable()
            ])
        );

        $partial_left_storage = new DynamicFunctionStorage();
        $partial_left_storage->templates = self::getTemplates($template_provider, $partial_function_storage);
        $partial_left_storage->params = [$partial_function_param, ...$fixed_params];
        $partial_left_storage->return_type = new Type\Union([
            new Type\Atomic\TClosure('Closure', $rest_params, $mapped_return_type)
        ]);

        return $partial_left_storage;
    }

    /**
     * @return null|list<Type\Atomic\TTemplateParam>
     */
    private static function getTemplates(
        DynamicTemplateProvider $template_provider,
        FunctionLikeStorage $partial_function_storage
    ): ?array {
        if (!$partial_function_storage->template_types) {
            return null;
        }

        return array_map(
            fn(int $offset) => $template_provider->createTemplate('T' . $offset),
            range(0, count($partial_function_storage->template_types) - 1)
        );
    }

    /**
     * @param list<Union> $types
     * @return list<FunctionLikeParameter>
     */
    private static function toParamList(array $types): array
    {
        return array_map(
            function (Type\Union $type, int $offset) {
                $param = new FunctionLikeParameter('p_' . $offset, false, $type);
                $param->is_optional = false;

                return $param;
            },
            $types,
            array_keys($types),
        );
    }

    private static function getPartialFunctionStorage(
        StatementsSource $source,
        Expr $func
    ): ?FunctionLikeStorage {
        if (!$source instanceof StatementsAnalyzer) {
            return null;
        }

        $codebase = $source->getCodebase();

        // Handle old way callable reference. i.e: partialLeft('map', fn($i) => $i + 1)
        if ($func instanceof PhpParser\Node\Scalar\String_ && !empty($func->value)) {
            $function_id = strtolower($func->value);

            return !empty($function_id)
                ? $codebase->functions->getStorage($source, $function_id)
                : null;
        }

        // Handle first class callable. i.e: partialLeft(map(...), fn($i) => $i + 1)
        if ($func instanceof PhpParser\Node\Expr\FuncCall && $func->isFirstClassCallable()) {
            $function_id = strtolower((string)$func->name->getAttribute('resolvedName'));

            return !empty($function_id)
                ? $codebase->functions->getStorage($source, $function_id)
                : null;
        }

        return null;
    }

    /**
     * We have: `map<A, B>(list<A>, callable(A): B): list<B>`
     * We call partialRight(map(...), fn(int $i) => $i + 1)
     * We need to remap all the `map` templates to the `partialRight` lower bounds.
     * I.e: ['A' => 'T0', 'B' => 'T1']
     */
    private static function getMappedLowerBounds(
        DynamicTemplateProvider $template_provider,
        FunctionLikeStorage $function_storage
    ): TemplateResult {
        $offset = 0;
        $lower_bounds = [];

        foreach ($function_storage->template_types ?? [] as $param_name => $for_class) {
            foreach (array_keys($for_class) as $defining_class) {
                $lower_bounds[$param_name][$defining_class] = new Type\Union([
                    $template_provider->createTemplate('T' . ($offset++))
                ]);
            }
        }

        return new TemplateResult([], $lower_bounds);
    }

    /**
     * It returns `[list<T0>, callable(T0): T1]` from `map<A, B>(list<A>, callable(A): B): list<B>`
     *
     * @return list<Union>
     */
    private static function mapParamTypes(
        Codebase $codebase,
        FunctionLikeStorage $storage,
        TemplateResult $template_result
    ): array {
        return array_map(
            function (FunctionLikeParameter $param) use ($template_result, $codebase) {
                $param_type = $param->type ?? Type::getMixed();

                return TemplateInferredTypeReplacer::replace($param_type, $template_result, $codebase);
            },
            $storage->params
        );
    }

    /**
     * It returns `list<T1>`
     * from `map<A, B>(list<A>, callable(A): B): list<B>`
     */
    private static function mapReturnType(
        Codebase $codebase,
        FunctionLikeStorage $storage,
        TemplateResult $template_result
    ): Type\Union {
        if (!$storage->return_type) {
            return Type::getMixed();
        }

        return TemplateInferredTypeReplacer::replace($storage->return_type, $template_result, $codebase);
    }
}
